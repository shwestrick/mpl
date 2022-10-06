(* Author: Sam Westrick (swestric@cs.cmu.edu) *)

(* Scheduler implements a single structure.
 *   ForkJoin : FORK_JOIN
 * It is pulled out of Scheduler at the bottom of this file. *)
structure Scheduler =
struct

  val _ = print ("J DEBUGGING\n")

  fun arraySub (a, i) = Array.sub (a, i)
  fun arrayUpdate (a, i, x) = Array.update (a, i, x)
  fun vectorSub (v, i) = Vector.sub (v, i)

  val P = MLton.Parallel.numberOfProcessors
  val myWorkerId = MLton.Parallel.processorNumber

  fun die strfn =
    ( print (Int.toString (myWorkerId ()) ^ ": " ^ strfn () ^ "\n")
    ; OS.Process.exit OS.Process.failure
    )

  fun search key args =
    case args of
      [] => NONE
    | x :: args' =>
        if key = x
        then SOME args'
        else search key args'

  fun parseFlag key =
    case search ("--" ^ key) (CommandLine.arguments ()) of
      NONE => false
    | SOME _ => true

  fun parseInt key default =
    case search ("-" ^ key) (CommandLine.arguments ()) of
      NONE => default
    | SOME [] => die (fn _ => "Missing argument of \"-" ^ key ^ "\" ")
    | SOME (s :: _) =>
        case Int.fromString s of
          NONE => die (fn _ => "Cannot parse integer from \"-" ^ key ^ " " ^ s ^ "\"")
        | SOME x => x

  (* val activatePar = parseFlag "activate-par" *)
  val heartbeatMicroseconds =
    LargeInt.fromInt (parseInt "heartbeat-us" 1000)

  structure Queue = DequeABP (*ArrayQueue*)

  val pcall = _prim "PCall":
    ('a -> 'b)      (* left side *)
    * 'a            (* left side argument *)
    * ('b -> 'c)    (* sequential left-side continuation *)
    * ('b -> 'c)    (* parallel left-side continuation (left-side sync code) *)
    * ('d -> 'e)    (* parallel right-side task (+right-side sync code), no return allowed! *)
    * 'd            (* parallel right-side argument *)
    -> 'c;


  structure Thread = MLton.Thread.Basic
  (* val setSimpleSignalHandler = MLton.Thread.setSimpleSignalHandler *)
  (* fun threadSwitch t =
    ( Thread.atomicBegin ()
    ; Thread.switchTo t
    ) *)

  fun assertAtomic msg x =
    let
      val ass = Word32.toInt (Thread.atomicState ())
    in
      if ass = x then ()
      else die (fn _ => "scheduler bug: " ^ msg ^ ": atomic " ^ Int.toString ass ^ " but expected " ^ Int.toString x)
    end

  fun threadSwitchEndAtomic t =
    ( if Thread.atomicState () <> 0w0 then ()
      else die (fn _ => "scheduler bug: threadSwitchEndAtomic while non-atomic")
    ; Thread.switchTo t
    )

  structure HM = MLton.HM
  structure HH = MLton.Thread.HierarchicalHeap
  type hh_address = Word64.word
  type gctask_data = Thread.t * (hh_address ref)

  structure DE = MLton.Thread.Disentanglement

  local
    (** See MAX_FORK_DEPTH in runtime/gc/decheck.c *)
    val maxDisetanglementCheckDepth = DE.decheckMaxDepth ()
  in
  fun depthOkayForDECheck depth =
    case maxDisetanglementCheckDepth of
      (* in this case, there is no entanglement detection, so no problem *)
      NONE => true

      (* entanglement checks are active, and the max depth is m *)
    | SOME m => depth < m
  end

  val internalGCThresh = Real.toInt IEEEReal.TO_POSINF
                          ((Math.log10(Real.fromInt P)) / (Math.log10 (2.0)))

  (* val vcas = MLton.Parallel.arrayCompareAndSwap *)
  (* fun cas (a, i) (old, new) = (vcas (a, i) (old, new) = old) *)
  fun faa (r, d) = MLton.Parallel.fetchAndAdd r d
  fun casRef r (old, new) =
    (MLton.Parallel.compareAndSwap r (old, new) = old)

  fun decrementHitsZero (x : int ref) : bool =
    faa (x, ~1) = 1


  datatype gc_joinpoint =
    GCJ of {gcTaskData: gctask_data option}
    (** The fact that the gcTaskData is an option here is a questionable
      * hack... the data will always be SOME. But unwrapping it may affect
      * how many allocations occur when spawning a gc task, which in turn
      * affects the GC snapshot, which is already murky.
      *)

  datatype 'a joinpoint =
    J of
      { leftSideThread: Thread.t
      , rightSideThread: Thread.t option ref
      , rightSideResult: 'a Result.t option ref
      , incounter: int ref
      , tidRight: Word64.word
      , gcj: gc_joinpoint option
      }


  (* ========================================================================
   * DEBUGGING
   *)

  val doDebugMsg = false

  val printLock : Word32.word ref = ref 0w0
  val _ = MLton.Parallel.Deprecated.lockInit printLock
  fun dbgmsg m =
    if not doDebugMsg then () else
    let
      val p = myWorkerId ()
      val _ = MLton.Parallel.Deprecated.takeLock printLock
      val msg = String.concat ["[", Int.toString p, "] ", m(), "\n"]
    in
      ( TextIO.output (TextIO.stdErr, msg)
      ; TextIO.flushOut TextIO.stdErr
      ; MLton.Parallel.Deprecated.releaseLock printLock
      )
    end

  fun dbgmsg' m =
    let
      val p = myWorkerId ()
      (* val _ = MLton.Parallel.Deprecated.takeLock printLock *)
      val msg = String.concat ["[", Int.toString p, "] ", m(), "\n"]
    in
      ( TextIO.output (TextIO.stdErr, msg)
      ; TextIO.flushOut TextIO.stdErr
      (* ; MLton.Parallel.Deprecated.releaseLock printLock *)
      )
    end

  fun dbgmsg' _ = ()


  fun dbgmsg'' m =
    let
      val p = myWorkerId ()
      (* val _ = MLton.Parallel.Deprecated.takeLock printLock *)
      val msg = String.concat ["[", Int.toString p, "] ", m(), "\n"]
    in
      ( TextIO.output (TextIO.stdErr, msg)
      ; TextIO.flushOut TextIO.stdErr
      (* ; MLton.Parallel.Deprecated.releaseLock printLock *)
      )
    end

  (* ========================================================================
   * Activators and activator stacks
   *)

  type joinslot_id = Word64.word (* for debugging *)

  val joinslotIds: joinslot_id array =
    Array.tabulate (P, Word64.fromInt)

  fun nextJoinSlotId p =
    let
      val old = Array.sub (joinslotIds, p)
      val oldCount = Word64.div (old, Word64.fromInt P)
      val new = Word64.fromInt P * (oldCount + 0w1) + Word64.fromInt p
    in
      Array.update (joinslotIds, p, new);
      old
    end

  type stackelem = joinslot_id * (Thread.t -> bool)
  structure Stack = MkStack(type elem = stackelem)

  datatype joinslot_stack =
    JStack of { stack: Stack.t }

  fun maybeActivateOne s (t: Thread.t) =
    case Stack.peekOldest s of
      SOME (_, f) =>
        if f t then (Stack.popOldest s; ()) else ()
    | NONE => ()

  fun jstackNew () =
    JStack {stack = Stack.new ()}

  val jstacks: joinslot_stack option array =
    Array.tabulate (P, fn _ => NONE)


  (** SAM_NOTE: TODO: these functions are problematic for the write barrier.
    * The astack needs to be integrated with GC. Perhaps installed as a
    * special field of a thread? That would be nasty. *)
  fun jstackSetCurrent astack =
    ( dbgmsg' (fn _ => "set astack")
    ; Array.update (jstacks, myWorkerId (), SOME astack)
    )
  fun jstackSetCurrentNew t =
    ( dbgmsg' (fn _ => "set fresh astack")
    ; let
        val j as JStack {stack=jstack} = jstackNew ()
      in
        Stack.register (t, jstack);
        Array.update (jstacks, myWorkerId (), SOME j)
      end
    )

  fun jstackMaybeGetCurrent t =
    case Array.sub (jstacks, myWorkerId ()) of
      NONE => NONE
    | SOME (j as JStack {stack=j1}) =>
        let
          val j2 = Stack.current t
        in
          if Stack.same (j1, j2) then () else
            die (fn _ => "bug: Scheduler.jstackMaybeGetCurrent: mismatch");
          SOME j
        end

  fun jstackGetCurrent t =
    case Array.sub (jstacks, myWorkerId ()) of
      SOME (j as JStack {stack=j1}) =>
        let
          val j2 = Stack.current t
        in
          if Stack.same (j1, j2) then () else
            die (fn _ => "bug: Scheduler.jstackGetCurrent: mismatch");
          j
        end
    | NONE => die (fn _ => "bug: Scheduler.jstackGetCurrent: expected astack; found none")

  fun jstackTakeCurrent t =
    let
      val _ = Thread.atomicBegin ()
      val a = jstackGetCurrent t
    in
      Array.update (jstacks, myWorkerId (), NONE);
      Thread.atomicEnd ();
      a
    end

  fun jstackPush t x =
    let
      val _ = Thread.atomicBegin ()
      val JStack {stack, ...} = jstackGetCurrent t
      (* val c = !pushCounter *)
    in
      Stack.push (x, stack);
      Thread.atomicEnd ()
    end

  fun jstackPop t =
    let
      val _ = Thread.atomicBegin ()
      val JStack {stack, ...} = jstackGetCurrent t
      val result = Stack.pop stack
      val _ = dbgmsg'' (fn _ => "jstack size after pop: " ^ Int.toString (Stack.currentSize stack))
    in
      Thread.atomicEnd ();
      result
    end

  fun handler msg =
    MLton.Signal.Handler.inspectInterrupted (fn thread: Thread.t =>
      case jstackMaybeGetCurrent thread of
        NONE =>
          dbgmsg' (fn _ => msg ^ ": no current astack")
      | SOME (JStack {stack, ...}) =>
          ( ()
          ; dbgmsg' (fn _ =>
              msg
              ^ ": current astack size: "
              ^ Int.toString (Stack.currentSize stack))
          ; maybeActivateOne stack thread
          ))

  (** itimer is used to deliver signals regularly. sigusr1 is used to relay
    * these to all processes
    *)
  val _ = MLton.Signal.setHandler
    ( MLton.Itimer.signal MLton.Itimer.Real
    , handler "SIGALRM"
    )
  val _ = MLton.Signal.setHandler
    ( Posix.Signal.usr1
    , handler "SIGUSR1"
    )

  structure JoinSlot :>
  sig
    type 'a t
    datatype 'a status = Empty | Full of 'a joinpoint

    val make: Thread.t -> ('a t -> Thread.t -> bool) -> 'a t
    val cancel: Thread.t -> 'a t -> 'a status
    val put: 'a t * 'a joinpoint -> unit
    val markUnsuccessful: 'a t -> unit
    val get: 'a t -> 'a joinpoint
  end =
  struct
    datatype 'a internal_status = JNone | JSome of 'a joinpoint | JCancelled | JUnsuccessfulSpawn
    datatype 'a status = Empty | Full of 'a joinpoint
    datatype 'a t = T of joinslot_id * ('a internal_status ref)

    fun make t (doSpawn: 'a t -> Thread.t -> bool) =
      let
        val j: 'a internal_status ref = ref JNone
        val jid = nextJoinSlotId (myWorkerId ())
        val result = T (jid, j)
      in
        dbgmsg'' (fn _ => "making " ^ Word64.toString jid);
        jstackPush t (jid, doSpawn result);
        result
      end

    fun cancel t (T (jid, j)) =
      ( ()

      ; case jstackPop t of
          NONE => ()
            (* (case !j of JSome _ => () | _ => die (fn _ => "scheduler bug: non-full popped join")) *)
        | SOME (jid', _) =>
            if jid = jid' then ()
            else die (fn _ => "scheduler bug: activator pop mismatch")

      ; case !j of
          JNone =>
            ( dbgmsg'' (fn _ => "cancelling " ^ Word64.toString jid ^ ": no spawn")
            ; j := JCancelled
            ; Empty
            )
        | JUnsuccessfulSpawn =>
            ( dbgmsg'' (fn _ => "cancelling " ^ Word64.toString jid ^ ": unsuccessful spawn")
            ; j := JCancelled
            ; Empty
            )
        | JSome jp =>
            ( dbgmsg'' (fn _ => "cancelling " ^ Word64.toString jid ^ ": spawned")
            (* ; j := JCancelled *)
            ; Full jp
            )
        | JCancelled => die (fn _ => "scheduler bug: double join cancel")
      )

    fun put (T (jid, jor), j) =
      let
        val _ = dbgmsg'' (fn _ => "putting " ^ Word64.toString jid)
        val _ =
          case !jor of
            JCancelled => die (fn _ => "scheduler bug: join put after cancel")
          | JUnsuccessfulSpawn => die (fn _ => "scheduler bug: join put after unsuccessful spawn")
          | JSome _ => die (fn _ => "scheduler bug: join double put")
          | JNone => ()
      in
        jor := JSome j
      end

    fun get (T (jid, jor)) =
      ( dbgmsg'' (fn _ => "getting " ^ Word64.toString jid)
      ; case !jor of
          JSome j => j
        | JNone => die (fn _ => "scheduler bug: JoinSlot.get on NONE")
        | JUnsuccessfulSpawn => die (fn _ => "scheduler bug: get after unsuccessful spawn")
        | JCancelled => die (fn _ => "scheduler bug: get cancelled")
      )

    fun markUnsuccessful (T (jid, jor)) =
      let
        val _ = dbgmsg'' (fn _ => "marking unsuccessful " ^ Word64.toString jid)
        val _ =
          case !jor of
            JCancelled => die (fn _ => "scheduler bug: join mark unsuccessful after cancel")
          | JUnsuccessfulSpawn => die (fn _ => "scheduler bug: double mark unsuccessful")
          | JSome _ => die (fn _ => "scheduler bug: join mark unsuccessful after put")
          | JNone => ()
      in
        jor := JUnsuccessfulSpawn
      end
  end

  (* ========================================================================
   * TASKS
   *)

  datatype task =
    (* NormalTask of unit -> unit *)
    Continuation of Thread.t * int
  | NewThread of Thread.p * int
  | GCTask of gctask_data

  (* ========================================================================
   * IDLENESS TRACKING
   *)

  val idleTotals = Array.array (P, Time.zeroTime)
  fun getIdleTime p = arraySub (idleTotals, p)
  fun updateIdleTime (p, deltaTime) =
    arrayUpdate (idleTotals, p, Time.+ (getIdleTime p, deltaTime))

(*
  val timerGrain = 256
  fun startTimer myId = (myId, 0, Time.now ())
  fun tickTimer (p, count, t) =
    if count < timerGrain then (p, count+1, t) else
    let
      val t' = Time.now ()
      val diff = Time.- (t', t)
      val _ = updateIdleTime (p, diff)
    in
      (p, 0, t')
    end
  fun stopTimer (p, _, t) =
    (tickTimer (p, timerGrain, t); ())
*)

  fun startTimer _ = ()
  fun tickTimer _ = ()
  fun stopTimer _ = ()

  (** ========================================================================
    * MAXIMUM FORK DEPTHS
    *)

  val maxForkDepths = Array.array (P, 0)

  fun maxForkDepthSoFar () =
    Array.foldl Int.max 0 maxForkDepths

  fun recordForkDepth d =
    let
      val p = myWorkerId ()
    in
      if arraySub (maxForkDepths, p) >= d then
        ()
      else
        arrayUpdate (maxForkDepths, p, d)
    end

  (* ========================================================================
   * CHILD TASK PROTOTYPE THREAD
   *
   * this widget makes it possible to create new "user" threads by copying
   * the prototype thread, which immediately pulls a task out of the
   * current worker's task-box and then executes it.
   *)

  local
    val amOriginal = ref true
    val taskBoxes = Array.array (P, NONE)
    fun upd i x = HM.arrayUpdateNoBarrier (taskBoxes, i, x)
    fun sub i = HM.arraySubNoBarrier (taskBoxes, i)
  in
  val _ = Thread.copyCurrent ()
  val prototypeThread : Thread.p =
    if !amOriginal then
      (amOriginal := false; Thread.savedPre ())
    else
      case sub (myWorkerId ()) of
        NONE => die (fn _ => "scheduler bug: task box is empty")
      | SOME t =>
          ( upd (myWorkerId ()) NONE
          ; t () handle _ => ()
          ; die (fn _ => "scheduler bug: child task didn't exit properly")
          )
  fun setTaskBox p t =
    upd p (SOME t)
  end

  (* ========================================================================
   * SCHEDULER LOCAL DATA
   *)

  type worker_local_data =
    { queue : task Queue.t
    , schedThread : Thread.t option ref
    , gcTask: gctask_data option ref
    }

  fun wldInit p : worker_local_data =
    { queue = Queue.new ()
    , schedThread = ref NONE
    , gcTask = ref NONE
    }

  val workerLocalData = Vector.tabulate (P, wldInit)

  fun setGCTask p data =
    #gcTask (vectorSub (workerLocalData, p)) := data

  fun getGCTask p =
    ! (#gcTask (vectorSub (workerLocalData, p)))

  fun setQueueDepth p d =
    let
      val {queue, ...} = vectorSub (workerLocalData, p)
    in
      Queue.setDepth queue d
    end

  fun trySteal p =
    let
      val {queue, ...} = vectorSub (workerLocalData, p)
    in
      if not (Queue.pollHasWork queue) then
        NONE
      else
        Queue.tryPopTop queue
    end

  fun communicate () = ()

  fun push x =
    let
      val myId = myWorkerId ()
      val {queue, ...} = vectorSub (workerLocalData, myId)
    in
      Queue.pushBot queue x
    end

  fun clear () =
    let
      val myId = myWorkerId ()
      val {queue, ...} = vectorSub (workerLocalData, myId)
    in
      Queue.clear queue
    end

  fun pop () =
    let
      val myId = myWorkerId ()
      val {queue, ...} = vectorSub (workerLocalData, myId)
    in
      Queue.popBot queue
    end

  fun popDiscard () =
    case pop () of
      NONE => false
    | SOME _ => true

  fun returnToSchedEndAtomic () =
    let
      val myId = myWorkerId ()
      val {schedThread, ...} = vectorSub (workerLocalData, myId)
      val _ = dbgmsg'' (fn _ => "return to sched")
    in
      threadSwitchEndAtomic (Option.valOf (HM.refDerefNoBarrier schedThread))
    end

  (* ========================================================================
   * FORK JOIN
   *)

  structure ForkJoin =
  struct

    val communicate = communicate
    val getIdleTime = getIdleTime

    val maxPermittedCCDepth = 3

    fun spawnGC interruptedThread : gc_joinpoint option =
      let
        val thread = Thread.current ()
        val depth = HH.getDepth thread
      in
        if depth > maxPermittedCCDepth then
          NONE
        else
          let
            (** SAM_NOTE: atomic begin/end not needed here, becuase this is
              * already run in signal handler.
              *)

            val heapId = ref (HH.getRoot thread)
            val gcTaskTuple = (interruptedThread, heapId)
            val gcTaskData = SOME gcTaskTuple
            val gcTask = GCTask gcTaskTuple
            val cont_arr1 = ref NONE
            val cont_arr2 = ref NONE
            val cont_arr3 = ref (SOME (fn _ => (gcTask, gcTaskData))) (* a hack, I hope it works. *)

            (** The above could trigger a local GC and invalidate the hh
              * identifier... :'(
              *)
            val _ = heapId := HH.getRoot thread
          in
            if not (HH.registerCont (cont_arr1, cont_arr2, cont_arr3, thread)) then
              NONE
            else
              let
                val _ = push gcTask
                val _ = HH.setDepth (thread, depth + 1)
                val _ = HH.forceLeftHeap(myWorkerId(), thread)
              in
                SOME (GCJ {gcTaskData = gcTaskData})
              end
          end
      end


    fun syncGC (GCJ {gcTaskData}) =
      let
        val _ = Thread.atomicBegin ()
        val thread = Thread.current ()
        val depth = HH.getDepth thread
        val newDepth = depth-1
      in
        if popDiscard() then
          ( ()
          ; dbgmsg' (fn _ => "switching to do some GC stuff")
          ; setGCTask (myWorkerId ()) gcTaskData (* This communicates with the scheduler thread *)
          ; let
              val a = jstackTakeCurrent thread
            in
              push (Continuation (thread, newDepth))
              ; assertAtomic "syncGC before returnToSched" 1
              ; returnToSchedEndAtomic ()
              ; assertAtomic "syncGC after returnToSched" 1
              ; jstackSetCurrent a
            end
          ; dbgmsg' (fn _ => "back from GC stuff")
          )
        else
          ( clear()
          ; setQueueDepth (myWorkerId ()) newDepth
          );

        HH.promoteChunks thread;
        HH.setDepth (thread, newDepth);
        assertAtomic "syncGC done" 1;
        Thread.atomicEnd ()
      end


    (* runs in signal handler *)
    fun spawn
        (joinslot: 'b JoinSlot.t)
        (interruptedLeftThread: Thread.t) : bool
      =
      let
        val depth = HH.getDepth (Thread.current ())
      in
        if depth >= Queue.capacity orelse not (depthOkayForDECheck depth)
        then
          ( JoinSlot.markUnsuccessful joinslot
          ; true
          )
        else

        (* SAM_NOTE:
         * set new thread ->bytesNeeded to 0 (MLton makes no
         * assumptions about how much space is available for threads that
         * are about to return from pcall, which the new thread will appear
         * to do, by taking the top frame in forkThread.)
         *
         * set exnStack to 0. This is okay because the right-side should
         * never raise an exception. (The right-side should never actually
         * return to its parent frame, neither should it raise an exception,
         * expecting it to be caught by parent.)
         *
         * copy sync depths!
         *)

        (* SAM_NOTE: instantiate new thread with singleton joinslot stack,
         * and then make sure the first thing it does (when it executes)
         * is pop.
         *)
        case HH.forkThread interruptedLeftThread of

          (** this is the edge case, where spawn signal happens inbetween
            * JoinSlot.make and pcall
            *)
          NONE => false

        | SOME rightSideThread =>
            let
              val gcj = spawnGC interruptedLeftThread

              val _ = assertAtomic "spawn after spawnGC" 1

              val thread = Thread.current ()
              (* val astack = jstackGetCurrent () *)
              val depth = HH.getDepth thread

              val _ = dbgmsg'' (fn _ => "spawning at depth " ^ Int.toString depth)

              val rightSideThreadSlot = ref (NONE: Thread.t option)
              val rightSideResult = ref (NONE: 'b Result.t option)
              val incounter = ref 2

              val (tidLeft, tidRight) = DE.decheckFork ()

              val jp =
                J { leftSideThread = interruptedLeftThread
                  , rightSideThread = rightSideThreadSlot
                  , rightSideResult = rightSideResult
                  , incounter = incounter
                  , tidRight = tidRight
                  , gcj = gcj
                  }

              (* SAM_NOTE: when we make special runtime support for joinslots,
               * make sure we put in interruptedLeftThread's joinslot stack
               *)
              val _ = JoinSlot.put (joinslot, jp)

              (* double check... hopefully correct, not off by one? *)
              val _ = push (NewThread (rightSideThread, depth))
              val _ = HH.setDepth (thread, depth + 1)

              (* NOTE: off-by-one on purpose. Runtime depths start at 1. *)
              val _ = recordForkDepth depth

              val _ = DE.decheckSetTid tidLeft
              val _ = assertAtomic "spawn done" 1
            in
              true
            end
      end


    (** Must be called in an atomic section. Implicit atomicEnd() *)
    fun syncEndAtomic
        (J {rightSideThread, rightSideResult, incounter, tidRight, gcj, ...})
        g
      =
      let
        val _ = assertAtomic "syncEndAtomic begin" 1

        val thread = Thread.current ()
        val depth = HH.getDepth thread
        val newDepth = depth-1
        val tidLeft = DE.decheckGetTid thread

        val result =
          (* SPACE LEAK SPACE LEAK
           * need to merge in the thread that we spawned.
           *
           * PERHAPS TODO: just get rid of this fast path. it's not important
           * for efficiency anymore.
           *)
          if popDiscard () then
            ( dbgmsg'' (fn _ => "popDiscard success at depth " ^ Int.toString depth)
            ; HH.promoteChunks thread
            ; HH.setDepth (thread, newDepth)
            ; DE.decheckJoin (tidLeft, tidRight)
            ; Thread.atomicEnd ()
            ; let
                val gr = Result.result g
              in
                (* (gr, DE.decheckGetTid thread) *)
                gr
              end
            )
          else
            ( clear () (* this should be safe after popDiscard fails? *)

            ; let
                (** conservatively dispose of current activation stack,
                  * in anticipation of other processor taking over (in the
                  * case that we return to sched)
                  *)
                val a = jstackTakeCurrent thread
              in
                if decrementHitsZero incounter then
                  ()
                else
                  ( ()
                    (** Atomic 1 *)
                  ; assertAtomic "syncEndAtomic before returnToSched" 1
                  ; returnToSchedEndAtomic ()
                  ; assertAtomic "syncEndAtomic after returnToSched" 1
                  );

                jstackSetCurrent a
              end

            ; case HM.refDerefNoBarrier rightSideThread of
                NONE => die (fn _ => "scheduler bug: join failed")
              | SOME rightSideThread =>
                  let
                    val tidRight = DE.decheckGetTid rightSideThread
                  in
                    HH.mergeThreads (thread, rightSideThread);
                    HH.promoteChunks thread;
                    HH.setDepth (thread, newDepth);
                    DE.decheckJoin (tidLeft, tidRight);
                    setQueueDepth (myWorkerId ()) newDepth;
                    case HM.refDerefNoBarrier rightSideResult of
                      NONE => die (fn _ => "scheduler bug: join failed: missing result")
                    | SOME gr =>
                        ( ()
                        ; assertAtomic "syncEndAtomic after merge" 1
                        ; Thread.atomicEnd ()
                        ; gr
                        )
                  end
            )
      in
        case gcj of
          NONE => ()
        | SOME gcj => syncGC gcj;

        result
      end


(*
    fun simplefork (f, g) =
      let
        (** This code is a bit deceiving in the sense that spawn and sync, as
          * defined here, are not as general as they might seem. This code is
          * only correct because each spawn is paired with exactly one sync,
          * in a nested fashion (for every spawn, any spawn after it on the
          * same thread must be sync'ed before the original spawn is sync'ed).
          *
          * Deviating from this will cause terrible things to happen.
          *)
        val j = spawn g
        val fr = Result.result f
        val gr = sync j
      in
        (Result.extractResult fr, Result.extractResult gr)
      end


    fun contBasedFork (f: unit -> 'a, g: unit -> 'b) =
      let
        val cont: ('a Result.t -> ('a * 'b)) ref =
          ref (fn fr => (Result.extractResult fr, g()))

        fun activate () =
          let
            val j = spawn g
          in
            cont := (fn fr =>
              let
                val gr = sync j
              in
                (Result.extractResult fr, Result.extractResult gr)
              end)
          end

        val _ = if activatePar then activate () else ()
        val fr = Result.result f
      in
        (!cont) fr
      end
*)


(*
    fun activatorBasedFork (f: unit -> 'a, g: unit -> 'b) =
      let
        val x = Activator.make (fn t => spawn g t)
        val _ = assertAtomic 0
        val fr = Result.result f
        val _ = Thread.atomicBegin ()
      in
        case Activator.cancel x of
          Activator.Pending =>
            ( ()
            ; Thread.atomicEnd ()
            ; assertAtomic 0
            ; (Result.extractResult fr, g ())
            )

        | Activator.Activated j =>
            let
              val gr = syncEndAtomic j
            in
              assertAtomic 0;
              (Result.extractResult fr, Result.extractResult gr)
            end
      end
*)


    fun pcallFork (f: unit -> 'a, g: unit -> 'b) =
      let
        (* val _ = Thread.atomicBegin () *)
        val t = Thread.current ()
        val j = JoinSlot.make t spawn

        fun leftSideSequentialCont fres = (
          (* (_import "XXYYZZ": unit -> unit;)(); *)
          (* what if signal handler (heartbeat) happens here?
           * it's okay because the pcall frame will be gone, so
           * `forkThread` won't spawn on this join slot, so spawn will
           * fail.
           *)
           (*...... *)
          case JoinSlot.cancel t j of
            JoinSlot.Empty =>
              ( ()
              (* ; assertAtomic "leftSideSequentialCont" 1 *)
              (* ; Thread.atomicEnd () *)
              ; (Result.extractResult fres, g ())
              )
          | JoinSlot.Full _ =>
              die (fn _ => "scheduler bug: leftSideSequentialCont full joinslot")
        )

        fun leftSideParCont fres =
          let
            val _ = dbgmsg'' (fn _ => "hello from left-side par continuation")
            val _ = Thread.atomicBegin ()
            val _ = assertAtomic "leftSideParCont" 1
          in
            case JoinSlot.cancel t j of
              JoinSlot.Empty =>
                die (fn _ => "scheduler bug: leftSideParCont empty joinslot")
            | JoinSlot.Full jp =>
                let
                  val gres = syncEndAtomic jp g
                in
                  (Result.extractResult fres, Result.extractResult gres)
                end
          end

        fun rightSide () =
          let
            val _ = assertAtomic "pcallFork rightside begin" 1
            val thread = Thread.current ()
            val depth = HH.getDepth thread
            val _ = HH.forceLeftHeap(myWorkerId(), thread)

            val _ = dbgmsg'' (fn _ => "rightside begin at depth " ^ Int.toString depth)
            val J {leftSideThread, rightSideThread, rightSideResult, tidRight, incounter, ...} =
              JoinSlot.get j
            val () = jstackSetCurrentNew thread
            val () = DE.decheckSetTid tidRight
            val _ = Thread.atomicEnd()

            val gr = Result.result g

            val _ = Thread.atomicBegin ()
            val depth' = HH.getDepth (Thread.current ())
            val _ =
              if depth = depth' then ()
              else die (fn _ => "scheduler bug: depth mismatch: rightside began at depth " ^ Int.toString depth ^ " and ended at " ^ Int.toString depth')

            val _ = dbgmsg'' (fn _ => "rightside done at depth " ^ Int.toString depth')
            val _ = assertAtomic "pcallFork rightside begin synchronize" 1

            (** Remove the jstack, don't need it. If we return to the
              * scheduler, we should guarantee we don't have a joinslot
              * stack. If we end up switching to some other thread, then that
              * thread will reassign its own astack.
              *)
            val _ = jstackTakeCurrent thread

            val _ = assertAtomic "pcallFork rightside after jstackTake" 1
          in
            rightSideThread := SOME thread;
            rightSideResult := SOME gr;

            if decrementHitsZero incounter then
              ( ()
              ; setQueueDepth (myWorkerId ()) depth
                (** Atomic 1 *)
              ; Thread.atomicBegin ()

                (** Atomic 2 *)

                (** (When sibling is resumed, it needs to be atomic 1.
                  * Switching threads is implicit atomicEnd(), so we need
                  * to be at atomic2
                  *)
              ; assertAtomic "pcallFork rightside switch-to-left" 2
              ; threadSwitchEndAtomic leftSideThread
              )
            else
              ( assertAtomic "pcallFork rightside before returnToSched" 1
              ; returnToSchedEndAtomic ()
              )
          end
      in
        pcall
          ( fn () =>
              let
                (* val _ = assertAtomic "pcall left-side begin" 1 *)
                (* val _ = Thread.atomicEnd () *)
                val r = Result.result f
              in
                (* (_import "AABBCC": unit -> unit;)(); *)
                (* assertAtomic "pcall left-side done" 0; *)
                (* Thread.atomicBegin(); *)
                r
              end
          , ()
          , leftSideSequentialCont
          , leftSideParCont
          , rightSide
          , ()
          )
      end


    fun fork (f, g) =
      (* contBasedFork (f, g) *)
      (* activatorBasedFork (f, g) *)
      pcallFork (f, g)

  end

  (* ========================================================================
   * WORKER-LOCAL SETUP
   *
   * We maintain a distinction between
   *   - "scheduler" threads, which never are migrated between processors and
   *   are used to acquire new work when the processor becomes idle, and
   *   - "user" threads, which run user code and are migrated between processors
   *)

  fun setupSchedLoop () =
    let
      val mySchedThread = Thread.current ()
      val _ = HH.setDepth (mySchedThread, 1)
      val _ = HH.setMinLocalCollectionDepth (mySchedThread, 2)

      val myId = myWorkerId ()
      val myRand = SMLNJRandom.rand (0, myId)
      (*val myRand = SimpleRandom.rand myId*)
      val {queue=myQueue, schedThread, ...} =
        vectorSub (workerLocalData, myId)
      val _ = schedThread := SOME mySchedThread

      val _ = Queue.setDepth myQueue 1
      val _ = Queue.register myQueue myId

      (* ------------------------------------------------------------------- *)

      fun randomOtherId () =
        (*let val other = SimpleRandom.boundedInt (0, P-1) myRand*)
        let val other = SMLNJRandom.randRange (0, P-2) myRand
        in if other < myId then other else other+1
        end

      fun request idleTimer =
        let
          fun loop tries it =
            if tries = P * 100 then
              (OS.Process.sleep (Time.fromNanoseconds (LargeInt.fromInt (P * 100)));
               loop 0 (tickTimer idleTimer))
            else
            let
              val friend = randomOtherId ()
            in
              case trySteal friend of
                NONE => loop (tries+1) (tickTimer idleTimer)
              | SOME (task, depth) => (task, depth, tickTimer idleTimer)
            end
        in
          loop 0 idleTimer
        end

      (* ------------------------------------------------------------------- *)

      fun afterReturnToSched () =
        case getGCTask myId of
          NONE => ( dbgmsg'' (fn _ => "back in sched; no GC task"); () )
        | SOME (thread, hh) =>
            ( dbgmsg'' (fn _ => "back in sched; found GC task")
            ; setGCTask myId NONE
            (* ; print ("afterReturnToSched: found GC task\n") *)
            ; HH.collectThreadRoot (thread, !hh)
            (* ; print ("afterReturnToSched: done with GC\n") *)
            ; case pop () of
                NONE => ()
              | SOME (Continuation (thread, _)) =>
                  ( ()
                  ; dbgmsg'' (fn _ => "resume task thread")
                  ; Thread.atomicBegin ()
                  ; Thread.atomicBegin ()
                  ; assertAtomic "afterReturnToSched before thread switch" 2
                  ; threadSwitchEndAtomic thread
                  ; afterReturnToSched ()
                  )
              | SOME _ =>
                  die (fn _ => "bug: Scheduler.afterReturnToSched: impossible")
            )

      fun acquireWork () : unit =
        let
          val idleTimer = startTimer myId
          val (task, depth, idleTimer') = request idleTimer
          val _ = stopTimer idleTimer'
        in
          case task of
            GCTask (thread, hh) =>
              ( HH.collectThreadRoot (thread, !hh)
              ; acquireWork ()
              )
          | Continuation (thread, depth) =>
              ( ()
              ; dbgmsg'' (fn _ => "stole continuation (" ^ Int.toString depth ^ ")")
              (* ; dbgmsg' (fn _ => "resume task thread") *)
              ; Queue.setDepth myQueue depth
              ; Thread.atomicBegin ()
              ; Thread.atomicBegin ()
              ; assertAtomic "acquireWork before thread switch" 2
              ; threadSwitchEndAtomic thread
              ; afterReturnToSched ()
              ; Queue.setDepth myQueue 1
              ; acquireWork ()
              )
          | NewThread (thread, depth) =>
              let
                val taskThread = Thread.copy thread
              in
                if depth >= 1 then () else
                  die (fn _ => "scheduler bug: acquired with depth " ^ Int.toString depth);
                Queue.setDepth myQueue (depth+1);
                HH.moveNewThreadToDepth (taskThread, depth);
                HH.setDepth (taskThread, depth+1);
                (* setTaskBox myId t; *)
                Thread.atomicBegin ();
                Thread.atomicBegin ();
                assertAtomic "acquireWork before thread switch" 2;
                threadSwitchEndAtomic taskThread;
                afterReturnToSched ();
                Queue.setDepth myQueue 1;
                acquireWork ()
              end
        end

    in
      (afterReturnToSched, acquireWork)
    end

  (* ========================================================================
   * INITIALIZATION
   *)

  fun sched () =
    let
      val (_, acquireWork) = setupSchedLoop ()
    in
      acquireWork ();
      die (fn _ => "scheduler bug: scheduler exited acquire-work loop")
    end
  val _ = MLton.Parallel.registerProcessorFunction sched

  val originalThread = Thread.current ()
  val _ =
    if HH.getDepth originalThread = 0 then ()
    else die (fn _ => "scheduler bug: root depth <> 0")
  val _ = HH.setDepth (originalThread, 1)

  (* implicitly attaches worker child heaps *)
  val _ = MLton.Parallel.initializeProcessors ()

  (* Copy the current thread in order to create a scheduler thread.
   * First, the `then` branch is executed by the original thread. Then we
   * switch to the fresh scheduler thread, which executes the `else` branch.
   * Finally, the scheduler switches back to the original thread, so that
   * it can continue exiting the main program. *)
  val amOriginal = ref true
  val _ = Thread.copyCurrent ()
  val _ =
    if !amOriginal then
      let
        val schedThread = Thread.copy (Thread.savedPre ())
        (* val schedHeap = HH.newHeap () *)
      in
        amOriginal := false;
        setQueueDepth (myWorkerId ()) 1;
        Thread.atomicBegin ();
        threadSwitchEndAtomic schedThread
      end
    else
      let
        val (afterReturnToSched, acquireWork) = setupSchedLoop ()
      in
        Thread.atomicBegin ();
        threadSwitchEndAtomic originalThread;
        afterReturnToSched ();
        setQueueDepth (myWorkerId ()) 1;
        acquireWork ();
        die (fn _ => "scheduler bug: scheduler exited acquire-work loop")
      end

  val _ = jstackSetCurrentNew originalThread

  val _ =
    MLton.Itimer.set (MLton.Itimer.Real,
      { interval = Time.fromMicroseconds heartbeatMicroseconds
      , value = Time.fromMicroseconds heartbeatMicroseconds
      })

end

structure ForkJoin :> FORK_JOIN =
struct
  open Scheduler.ForkJoin

  fun par (f, g) =
    fork (f, g)

  fun for (i, j) f = if i >= j then () else (f i; for (i+1, j) f)

  fun parfor grain (i, j) f =
    if j - i <= grain then
      for (i, j) f
    else
      let
        val mid = i + (j-i) div 2
      in
        par (fn _ => parfor grain (i, mid) f,
             fn _ => parfor grain (mid, j) f)
        ; ()
      end

  fun alloc n =
    let
      val a = ArrayExtra.Raw.alloc n
      val _ =
        if ArrayExtra.Raw.uninitIsNop a then ()
        else parfor 10000 (0, n) (fn i => ArrayExtra.Raw.unsafeUninit (a, i))
    in
      ArrayExtra.Raw.unsafeToArray a
    end

  val maxForkDepthSoFar = Scheduler.maxForkDepthSoFar
end
