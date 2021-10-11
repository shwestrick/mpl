(* Author: Sam Westrick (swestric@cs.cmu.edu) *)

(* Scheduler implements a single structure.
 *   ForkJoin : FORK_JOIN
 * It is pulled out of Scheduler at the bottom of this file. *)
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

  datatype task =
    NormalTask of (unit -> unit) * int
  | GCTask of Thread.t * Word64.word

  structure DE = MLton.Thread.Disentanglement
  (** See MAX_FORK_DEPTH in runtime/gc/decheck.c *)
  val maxDisetanglementCheckDepth = 31

  val P = MLton.Parallel.numberOfProcessors
  val internalGCThresh = Real.toInt IEEEReal.TO_POSINF
                          ((Math.log10(Real.fromInt P)) / (Math.log10 (2.0)))
  val myWorkerId = MLton.Parallel.processorNumber

  (* val vcas = MLton.Parallel.arrayCompareAndSwap *)
  (* fun cas (a, i) (old, new) = (vcas (a, i) (old, new) = old) *)
  fun faa (r, d) = MLton.Parallel.fetchAndAdd r d
  fun casRef r (old, new) =
    (MLton.Parallel.compareAndSwap r (old, new) = old)

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

(*
  fun dbgmsg' m =
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
*)

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
    fun upd i x = HM.arrayUpdateNoBarrier (taskBoxes, Int64.fromInt i, x)
    fun sub i = HM.arraySubNoBarrier (taskBoxes, Int64.fromInt i)
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
    }

  fun wldInit p : worker_local_data =
    { queue = Queue.new ()
    , schedThread = ref NONE
    }

  val workerLocalData = Vector.tabulate (P, wldInit)

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
      threadSwitch (Option.valOf (HM.refDerefNoBarrier schedThread))
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
        val parentHeap = HH.getCurrentHeap thread

        (** NOTE: these cannot be safely combined into a single ref. After
          * the join, reading the thread is safe because the thread object
          * is stored at a safe depth. But reading the result is entangled
          * until after the merge happens.
          *)
        val rightSideThread = ref (NONE: Thread.t option)
        val rightSideResult = ref (NONE: 'b result option)

        val leftSideResult = ref (NONE: 'a result option)
        val incounter = ref 2
        val (tidLeft, tidRight) = DE.decheckFork ()

        fun g' () =
          let
            val () = DE.copySyncDepthsFromThread (thread, depth+1)
            val () = DE.decheckSetTid tidRight
            val gr = result g
            val t = Thread.current ()
          in
            rightSideThread := SOME t;
            rightSideResult := SOME gr;
            if decrementHitsZero incounter then
              ( setQueueDepth (myWorkerId ()) (depth+1)
              ; threadSwitch thread
              )
            else
              returnToSched ()
          end

        val _ = push (NormalTask (g', depth))
        val _ = HH.setDepth (thread, depth + 1)

        (* NOTE: off-by-one on purpose. Runtime depths start at 1. *)
        val _ = recordForkDepth depth

        val tidLeft =
          ( DE.decheckSetTid tidLeft
          ; leftSideResult := SOME (result f)
          ; DE.decheckGetTid thread
          )

        val () =
          if popDiscard () then
            ( DE.decheckSetTid tidRight
            ; HH.newHeapForRightChild parentHeap
            ; rightSideResult := SOME (result g)
            ; DE.decheckJoin (tidLeft, DE.decheckGetTid thread)
            ; HH.mergeSibling parentHeap
            ; HH.promoteChunks thread
            ; HH.setDepth (thread, depth)
            )
          else
            ( clear () (* this should be safe after popDiscard fails? *)
            ; if decrementHitsZero incounter then () else returnToSched ()
            ; setQueueDepth (myWorkerId ()) depth
            ; case HM.refDerefNoBarrier rightSideThread of
                NONE => die (fn _ => "scheduler bug: join failed")
              | SOME t =>
                  ( DE.decheckJoin (tidLeft, DE.decheckGetTid t)
                  ; HH.mergeThreads (thread, t)
                  ; HH.promoteChunks thread
                  ; HH.setDepth (thread, depth)
                  )
            )

        val fr =
          case HM.refDerefNoBarrier leftSideResult of
            NONE => die (fn _ => "scheduler bug: join failed: missing left-side result")
          | SOME x => extractResult x
        val gr =
          case HM.refDerefNoBarrier rightSideResult of
            NONE => die (fn _ => "scheduler bug: join failed: missing right-side result")
          | SOME x => extractResult x
      in
        (fr, gr)
      end


    fun forkGC thread depth (f : unit -> 'a, g : unit -> 'b) =
      let
        val rootHH = HH.getCurrentHeap thread

        (* fun gcFunc() =
          ( HH.collectThreadRoot(thread, rootHH)
          ; returnToSched ()
          ) *)

        val gcTask = GCTask (thread, rootHH)
        val cont_arr1 = Array.array (1, SOME f)
        val cont_arr2 = Array.array (1, SOME g)
        val cont_arr3 = Array.array (1, SOME (fn _ => gcTask)) (* a hack, I hope it works. *)
      in
        if not (HH.registerCont (cont_arr1, cont_arr2, cont_arr3, thread)) then
          fork' {ccOkayAtThisDepth=false} (f, g)
        else
          let
            val _ = push gcTask
            val _ = HH.setDepth (thread, depth + 1)
            val _ = HH.forceLeftHeap(myWorkerId(), thread)
            val result = fork' {ccOkayAtThisDepth=false} (f, g)

            val _ =
              if popDiscard() then
                (* if depth = 1 then *)
                  HH.collectThreadRoot (thread, rootHH)
                (* else
                  HH.cancelCC (thread, rootHH) *)
              else
                ( clear()
                ; setQueueDepth (myWorkerId ()) depth
                )

            val _ = HH.promoteChunks thread
            val _ = HH.setDepth (thread, depth)
          in
            result
          end
      end

    and fork' {ccOkayAtThisDepth} (f, g) =
      let
        val thread = Thread.current ()
        val depth = HH.getDepth thread
      in
        (* if ccOkayAtThisDepth andalso depth = 1 then *)
        if ccOkayAtThisDepth andalso depth >= 1 andalso depth <= 3 then
          forkGC thread depth (f, g)
        else if depth < Queue.capacity andalso
                depth < maxDisetanglementCheckDepth then
          parfork thread depth (f, g)
        else
          (* don't let us hit an error, just sequentialize instead *)
          (f (), g ())
      end

    fun fork (f, g) = fork' {ccOkayAtThisDepth=true} (f, g)
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

      fun acquireWork () : unit =
        let
          val idleTimer = startTimer myId
          val (task, _, idleTimer') = request idleTimer
        in
          case task of
            GCTask (thread, hh) =>
              ( HH.collectThreadRoot (thread, hh)
              ; acquireWork ()
              )
          | NormalTask (t, depth) =>
              let
                val taskThread = Thread.copy prototypeThread
              in
                if depth >= 1 then () else
                  die (fn _ => "scheduler bug: acquired with depth " ^ Int.toString depth ^ "\n");
                Queue.setDepth myQueue (depth+1);
                HH.moveNewThreadToDepth (taskThread, depth);
                HH.setDepth (taskThread, depth+1);
                setTaskBox myId t;
                stopTimer idleTimer';
                threadSwitch taskThread;
                Queue.setDepth myQueue 1;
                acquireWork ()
              end
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
        threadSwitch schedThread
      end
    else
      let
        val acquireWork = setupSchedLoop ()
      in
        threadSwitch originalThread;
        setQueueDepth (myWorkerId ()) 1;
        acquireWork ();
        die (fn _ => "scheduler bug: scheduler exited acquire-work loop")
      end

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

  val maxForkDepthSoFar = Scheduler.maxForkDepthSoFar
end
