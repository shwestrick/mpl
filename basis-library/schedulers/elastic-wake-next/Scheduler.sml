(* Author: Sam Westrick (swestric@cs.cmu.edu)
 * This is modification of the ../shh scheduler, to make it elastic.
 *)

(* Scheduler implements a single structure.
 *   ForkJoin : FORK_JOIN
 * It is pulled out of Scheduler at the bottom of this file.
 *)
structure Scheduler =
struct

  fun arraySub (a, i) = Array.sub (a, i)
  fun arrayUpdate (a, i, x) = Array.update (a, i, x)
  fun vectorSub (v, i) = Vector.sub (v, i)

  structure Queue = DequeABP (*ArrayQueue*)

  structure Thread = MLton.Thread.Basic
  fun threadSwitch t =
    ( Thread.atomicBegin ()
    ; Thread.switchTo t
    )

  structure HM = MLton.HM
  structure HH = MLton.Thread.HierarchicalHeap

  val P = MLton.Parallel.numberOfProcessors
  val myWorkerId = MLton.Parallel.processorNumber

  (* val vcas = MLton.Parallel.arrayCompareAndSwap *)
  (* fun cas (a, i) (old, new) = (vcas (a, i) (old, new) = old) *)
  fun faa (r, d) = MLton.Parallel.fetchAndAdd r d
  fun casRef r (old, new) =
    (MLton.Parallel.compareAndSwap r (old, new) = old)

  fun casArray (a, i) (old, new) =
    (MLton.Parallel.arrayCompareAndSwap (a, i) (old, new) = old)

  fun decrementHitsZero (x : int ref) : bool =
    faa (x, ~1) = 1

  (* ========================================================================
   * DEBUGGING
   *)

  fun die strfn =
    ( print (Int.toString (myWorkerId ()) ^ ": " ^ strfn ())
    ; OS.Process.exit OS.Process.failure
    )

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

  (* ========================================================================
   * IDLENESS TRACKING
   *)

  val idleTotals = Array.array (P, Time.zeroTime)
  fun getIdleTime p = arraySub (idleTotals, p)
  fun updateIdleTime (p, deltaTime) =
    arrayUpdate (idleTotals, p, Time.+ (getIdleTime p, deltaTime))

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

  (*
  fun startTimer _ = ()
  fun tickTimer _ = ()
  fun stopTimer _ = ()
  *)

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
    fun upd i x = MLton.HM.arrayUpdateNoBarrier (taskBoxes, Int64.fromInt i, x)
  in
  val _ = Thread.copyCurrent ()
  val prototypeThread : Thread.p =
    if !amOriginal then
      (amOriginal := false; Thread.savedPre ())
    else
      case Array.sub (taskBoxes, myWorkerId ()) of
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
   * LIFELINES AND STATE MANAGEMENT
   *)

  fun hashWord w =
    let
      open Word64
      infix 2 >> infix 2 << infix 2 xorb infix 2 andb
      val v = w * 0w3935559000370003845 + 0w2691343689449507681
      val v = v xorb (v >> 0w21)
      val v = v xorb (v << 0w37)
      val v = v xorb (v >> 0w4)
      val v = v * 0w4768777513237032717
      val v = v xorb (v << 0w20)
      val v = v xorb (v >> 0w41)
      val v = v xorb (v << 0w5)
    in
      v
    end

  (* computes 1 + floor(log_2(n)), i.e. the number of
   * bits required to represent n in binary *)
  fun log2 n = if (n < 1) then 0 else 1 + log2(n div 2)

  val bitsChild = log2 P
  val childMask = Word64.- (Word64.<< (0w1, Word.fromInt bitsChild), 0w1)

  val bitsPriority = 64 - bitsChild - 1
  val priorityMask = Word64.- (Word64.<< (0w1, Word.fromInt bitsPriority), 0w1)

  type pstate = Word64.word
  type state = {rejecting: bool, priority: Word64.word, firstChild: int option}

  (* to pack and unpack states, we use this layout:
   *
   *   rejecting bit    priority       firstChild
   *        |              |                |
   *        v              v                v
   *      +---+---------------------+--------------+
   *      | 1 |   64 - log2 P - 1   |    log2 P    |
   *      +---+---------------------+--------------+
   *
   * and when there is no firstChild, we pack with a value that
   * is >= P (the number of processors).
   *)
  fun packState ({rejecting, priority, firstChild}: state) : pstate =
    let
      open Word64
      infix 2 >> << orb

      val rej = if rejecting then 0w1 else 0w0
      val prio =
        if priority <= priorityMask then priority
        else raise Fail "tried to pack priority outside valid range"
      val child =
        case firstChild of
          NONE => fromInt P
        | SOME p =>
            if Int.>= (p, 0) andalso Int.< (p, P) then fromInt p
            else raise Fail "tried to pack child number outside valid range"

      val ps: pstate = rej
      val ps = (ps << Word.fromInt bitsPriority) orb prio
      val ps = (ps << Word.fromInt bitsChild) orb child
    in
      ps
    end

  fun unpackState (ps: pstate) : state =
    let
      open Word64
      infix 2 >> << orb andb
      val firstChild =
        let val x = toInt (ps andb childMask)
        in if Int.>= (x, P) then NONE else SOME x
        end

      val ps = ps >> Word.fromInt bitsChild
      val priority = ps andb priorityMask

      val ps = ps >> Word.fromInt bitsPriority
      val rejecting = (ps andb 0w1) = 0w1
    in
      {rejecting=rejecting, priority=priority, firstChild=firstChild}
    end

  (* ========================================================================
   * CONCURRENT RANDOM SET
   *)

  structure CRS =
  struct
    (* Pad to avoid false sharing. Initially, everyone is awake *)
    val members: Word8.word array = Array.array (128*P, 0w1)

    fun insert id =
      Array.update (members, 128*id, 0w1)

    fun remove id =
      Array.update (members, 128*id, 0w0)

    fun sampleRandomOther myId (myRand: SimpleRandom.t): int =
      let
        fun loop () =
          let
            val p = SimpleRandom.boundedInt (0, P-1) myRand
            val p = if p < myId then p else p+1
          in
            if Array.sub (members, 128*p) = 0w0 then loop () else p
          end
      in
        loop ()
      end

  end

  (* ========================================================================
   * SCHEDULER LOCAL DATA
   *)

  type worker_local_data =
    { queue : (unit -> unit) Queue.t
    , schedThread : Thread.t option ref
    , state : pstate ref
    , next : int ref     (* processor id of next child in parent's list of
                          * children, or ~1 if end of list *)
    }

  fun initialState p =
    { rejecting = false
    , priority = Word64.andb (priorityMask, hashWord (Word64.fromInt p))
    , firstChild = NONE
    }

  fun wldInit p : worker_local_data =
    { queue = Queue.new ()
    , schedThread = ref NONE
    , state = ref (packState (initialState p))
    , next = ref ~1
    }

  val workerLocalData = Vector.tabulate (P, wldInit)

  fun state p = #state (vectorSub (workerLocalData, p))
  fun next p = #next (vectorSub (workerLocalData, p))

  fun addLifeline me them =
    let
      val myState = unpackState (!(state me))

      fun loop () =
        let
          val theirPackedState = !(state them)
          val theirState = unpackState theirPackedState
          val theirPackedState' = packState
            { rejecting = false
            , priority = #priority theirState
            , firstChild = SOME me }
          val nogo =
            (#rejecting theirState) orelse
            #priority myState >= #priority theirState
        in
          next me := Option.getOpt (#firstChild theirState, ~1);
          if nogo then
            false
          else if casRef (state them) (theirPackedState, theirPackedState') then
            true
          else
            loop ()
        end

    in
      if loop () then
        true
      else
        (next me := ~1; false)
    end

  fun wakeUpAFew n c =
    if n <= 1 then
      MLton.Parallel.semPost c
    else
      let
        val c' = !(next c)
      in
        if c' < 0 then () else next c := ~1;
        MLton.Parallel.semPost c;
        if c' < 0 then () else wakeUpAFew (n-1) c'
      end

  fun rejectLifelines p =
    let
      val packedState = !(state p)
      val {firstChild, priority, ...} = unpackState packedState
      val packedState' = packState
        { rejecting = true
        , priority = priority
        , firstChild = NONE
        }
    in
      if casRef (state p) (packedState, packedState') then
        Option.app (wakeUpAFew 4) firstChild
      else
        rejectLifelines p
    end

  fun acceptLifelines p =
    let
      val {priority, ...} = unpackState (!(state p))
      val newPriority =
        Word64.andb (priorityMask, hashWord (priority + Word64.fromInt p))
      val newState = packState
        { rejecting = false
        , priority = newPriority
        , firstChild = NONE
        }
    in
      state p := newState
    end

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

  fun popDiscard () =
    let
      val myId = myWorkerId ()
      val {queue, ...} = vectorSub (workerLocalData, myId)
    in
      case Queue.popBot queue of
          NONE => false
        | SOME _ => true
    end

  fun returnToSched () =
    let
      val myId = myWorkerId ()
      val {schedThread, ...} = vectorSub (workerLocalData, myId)
    in
      threadSwitch (Option.valOf (!schedThread))
    end

  (* ========================================================================
   * FORK JOIN
   *)

  structure ForkJoin =
  struct

    datatype 'a result =
      Finished of 'a
    | Raised of exn

    fun result f =
      Finished (f ()) handle e => Raised e

    fun extractResult r =
      case r of
        Finished x => x
      | Raised e => raise e

    val communicate = communicate
    val getIdleTime = getIdleTime

    (* Must be called from a "user" thread, which has an associated HH *)
    fun parfork thread depth (f : unit -> 'a, g : unit -> 'b) =
      let
        val rightSide = ref (NONE : ('b result * Thread.t) option)
        val incounter = ref 2

        fun g' () =
          let
            val gr = result g
            val t = Thread.current ()
          in
            rightSide := SOME (gr, t);
            if decrementHitsZero incounter then
              ( setQueueDepth (myWorkerId ()) (depth+1)
              ; threadSwitch thread
              )
            else
              returnToSched ()
          end

        val _ = push g'
        val _ = HH.setDepth (thread, depth + 1)

        val fr = result f

        val gr =
          if popDiscard () then
            ( HH.promoteChunks thread
            ; HH.setDepth (thread, depth)
            ; result g
            )
          else
            ( clear () (* this should be safe after popDiscard fails? *)
            ; if decrementHitsZero incounter then () else returnToSched ()
            ; case !rightSide of
                NONE => die (fn _ => "scheduler bug: join failed")
              | SOME (gr, t) =>
                  ( HH.mergeThreads (thread, t)
                  ; setQueueDepth (myWorkerId ()) depth
                  ; HH.promoteChunks thread
                  ; HH.setDepth (thread, depth)
                  ; gr
                  )
            )
      in
        (extractResult fr, extractResult gr)
      end

    fun fork (f, g) =
      let
        val thread = Thread.current ()
        val depth = HH.getDepth thread
      in
        (* don't let us hit an error, just sequentialize instead *)
        if depth < Queue.capacity then
          parfork thread depth (f, g)
        else
          (f (), g ())
      end
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
      val myId = myWorkerId ()
      (* val myRand = SMLNJRandom.rand (0, myId) *)
      val myRand = SimpleRandom.rand myId
      val mySchedThread = Thread.current ()
      val {queue=myQueue, schedThread, ...} =
        vectorSub (workerLocalData, myId)
      val _ = schedThread := SOME mySchedThread

      val _ = Queue.setDepth myQueue 1
      val _ = Queue.register myQueue myId

      (* ------------------------------------------------------------------- *)


      fun markAsleep () = CRS.remove myId
      fun markAwake () = CRS.insert myId
      fun randomOtherId () =
        CRS.sampleRandomOther myId myRand

      (*
      fun markAsleep () = ()
      fun markAwake () = ()
      fun randomOtherId () =
        let val other = SimpleRandom.boundedInt (0, P-1) myRand
        (* let val other = SMLNJRandom.randRange (0, P-2) myRand *)
        in if other < myId then other else other+1
        end
      *)

      fun wait () = MLton.Parallel.semWait myId

      fun tryWakeNext () =
        let
          val c = !(next myId)
        in
          if c < 0 then ()
          else (next myId := ~1; wakeUpAFew 4 c)
        end

      fun tryChill friend =
        if addLifeline myId friend then
          ( markAsleep ()
          ; wait ()
          ; markAwake ()
          ; tryWakeNext ()
          ; true
          )
        else
          false

      fun stealLoopChill idleTimer =
        let
          fun loop it =
            let
              val friend = randomOtherId ()
            in
              case trySteal friend of
                SOME (task, depth) => (task, depth, tickTimer idleTimer)
              | NONE =>
                  if tryChill friend then
                    stealLoopDontChill (tickTimer idleTimer)
                  else
                    loop (tickTimer idleTimer)
            end
        in
          loop idleTimer
        end

      and stealLoopDontChill idleTimer =
        let
          fun loop tries it =
            if tries >= 50 then
              stealLoopChill idleTimer
            else
              let
                val friend = randomOtherId ()
              in
                case trySteal friend of
                  SOME (task, depth) => (task, depth, tickTimer idleTimer)
                | NONE => loop (tries+1) (tickTimer idleTimer)
              end
        in
          loop 0 idleTimer
        end

      (* ------------------------------------------------------------------- *)

      fun acquireWork () : unit =
        let
          val idleTimer = startTimer myId
          val (task, depth, idleTimer') = stealLoopDontChill idleTimer
          val taskThread = Thread.copy prototypeThread
        in
          if depth >= 1 then () else
            die (fn _ => "scheduler bug: acquired with depth " ^ Int.toString depth ^ "\n");
          rejectLifelines myId;
          HH.setDepth (taskThread, depth+1);
          Queue.setDepth myQueue (depth+1);
          setTaskBox myId task;
          stopTimer idleTimer';
          threadSwitch taskThread;
          Queue.setDepth myQueue 1;
          acceptLifelines myId;
          acquireWork ()
        end

    in
      acquireWork
    end

  (* ========================================================================
   * INITIALIZATION
   *)

  fun sched () =
    let
      val acquireWork = setupSchedLoop ()
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

  (* initially, although the main worker needs to pop into the scheduler to
   * set up scheduler data, it is going to return immediately to do work,
   * so it should not accept any lifelines. *)
  val _ = rejectLifelines (myWorkerId ())

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
        HH.setDepth (schedThread, 1);
        setQueueDepth (myWorkerId ()) 1;
        threadSwitch schedThread
      end
    else
      let
        val acquireWork = setupSchedLoop ()
      in
        threadSwitch originalThread;
        setQueueDepth (myWorkerId ()) 1;
        acceptLifelines (myWorkerId ());
        acquireWork ();
        die (fn _ => "scheduler bug: scheduler exited acquire-work loop")
      end

  (* val _ = print ("hello from elastic\n") *)

end

structure ForkJoin :> FORK_JOIN =
struct
  open Scheduler.ForkJoin

  val par = fork

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
end
