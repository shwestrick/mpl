(* Author: Sam Westrick (swestric@cs.cmu.edu) *)

(* Scheduler implements a single structure.
 *   ForkJoin : FORK_JOIN
 * It is pulled out of Scheduler at the bottom of this file. *)
structure Scheduler =
struct

  fun arraySub (a, i) = Array.sub (a, i)
  fun arrayUpdate (a, i, x) = Array.update (a, i, x)
  fun vectorSub (v, i) = Vector.sub (v, i)

  structure Queue = ArrayQueue

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
   * SCHEDULER PUBLIC DATA
   *)

  (* A request is either REQUEST_NONE, REQUEST_BLOCKED, or a processor id.
   * Workers request work by writing their own id into another worker's
   * request cell. If a worker is idle, it blocks requests from other workers
   * by changing its own request cell to REQUEST_BLOCKED. *)
  val REQUEST_NONE = ~1
  val REQUEST_BLOCKED = ~2

  val MAIL_WAITING = 0
  val MAIL_RECEIVING = 1
  val MAIL_REJECT = 2

  val dummyTask = NONE
  val dummyHeap = MLton.Pointer.null

  type worker_public_data =
    { mailbox :
        { hbox : MLton.Pointer.t ref
        , tbox : (unit -> unit) option ref
        , flag : int ref
        }
    , hasWork : bool ref
    , request : int ref
    }

  val workerPublicData = Vector.tabulate (P, fn _ =>
    { mailbox =
        { hbox = ref dummyHeap
        , tbox = ref dummyTask
        , flag = ref MAIL_WAITING
        }
    , hasWork = ref false
    , request = ref REQUEST_NONE
    })

  fun wpd p = vectorSub (workerPublicData, p)

  fun checkHasWork p    = !(#hasWork (wpd p))
  fun setHasWork (p, s) = #hasWork (wpd p) := s

  fun getRequest p          = !(#request (wpd p))
  fun setRequest (p, r)     = #request (wpd p) := r
  fun casRequest (p, r, r') = casRef (#request (wpd p)) (r, r')

  fun mailbox p = #mailbox (wpd p)

  fun setHeapBox (p, h) = #hbox (mailbox p) := h

  fun getHeapBox p =
    let
      val box = #hbox (mailbox p)
      val h = !box
    in
      box := dummyHeap;
      h
    end

  fun setTaskBox (p, t) =
    #tbox (mailbox p) := t

  fun getTaskBox p =
    let
      val box = #tbox (mailbox p)
      val t = !box
    in
      box := dummyTask;
      t
    end

  fun setMailReceiving p =
    if casRef (#flag (mailbox p)) (MAIL_WAITING, MAIL_RECEIVING)
    then ()
    else die (fn _ => "scheduler error: set mailbox receiving failed")

  fun setMailReject p =
    if casRef (#flag (mailbox p)) (MAIL_WAITING, MAIL_REJECT)
    then ()
    else die (fn _ => "scheduler error: set mailbox reject failed")

  fun waitForMail p =
    let
      val flag = #flag (mailbox p)
      fun loop () =
        let
          val f = !flag
        in
          if f = MAIL_WAITING then
            loop ()
          else
            f = MAIL_RECEIVING
        end
      val result = loop ()
    in
      flag := MAIL_WAITING;
      result
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
  in
  val _ = Thread.copyCurrent ()
  val prototypeThread : Thread.p =
    if !amOriginal then
      (amOriginal := false; Thread.savedPre ())
    else
      case getTaskBox (myWorkerId ()) of
        NONE => die (fn _ => "scheduler bug: task box is empty")
      | SOME t =>
          ( t () handle _ => ()
          ; die (fn _ => "scheduler bug: child task didn't exit properly")
          )
  end

  (* ========================================================================
   * SCHEDULER FUNCTIONS
   *)

  (* val push : task -> unit
   * push onto the current work queue *)
  val pushFuncs = Array.array (P, fn _ => die (fn _ => "Error: dummy push"))
  fun push x = arraySub (pushFuncs, myWorkerId ()) x

  (* val popDiscard : unit -> bool
   * Attempts to pop a task off the task queue. If it fails (because the queue
   * is empty) then the desired task must have been served to another worker. *)
  val popDiscardFuncs = Array.array (P, fn _ => (die (fn _ => "Error: dummy popDiscard"); false))
  fun popDiscard () = arraySub (popDiscardFuncs, myWorkerId ()) ()

  val communicateFuncs = Array.array (P, fn _ => die (fn _ => "Error: dummy communicate"))
  fun schedCommunicate () = arraySub (communicateFuncs, myWorkerId ()) ()

  val returnToScheds = Array.array (P, fn _ => die (fn _ => "Error: dummy returnToSched"))
  fun returnToSched x = arraySub (returnToScheds, myWorkerId ()) x

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

    val communicate = schedCommunicate
    val getIdleTime = getIdleTime

    (* Must be called from a "user" thread, which has an associated HH *)
    fun fork (f : unit -> 'a, g : unit -> 'b) =
      let
        val thread = Thread.current ()
        val level = HH.getLevel thread

        val rightSide = ref (NONE : 'b result option)
        val incounter = ref 2

        fun g' () =
          ( rightSide := SOME (result g)
          ; returnToSched (incounter, thread)
          )

        val _ = push (g', level)
        val _ = HH.setLevel (thread, level + 1)

        val _ = communicate ()
        val fr = result f
        val _ = communicate ()

        val gr =
          if popDiscard () then
            result g
          else
            ( returnToSched (incounter, thread)
            ; HH.mergeDeepestChild thread
            ; case !rightSide of
                NONE => die (fn _ => "scheduler bug: join failed")
              | SOME gr => gr
            )

        val _ = HH.promoteChunks thread
        val _ = HH.setLevel (thread, level)
      in
        (extractResult fr, extractResult gr)
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
      val myQueue = Queue.new myId
      val myRand = SimpleRandom.rand myId
      val mySchedThread = Thread.current ()
      val myRetArg = ref NONE

      (* the lock is not necessary for private deques, but need to do this to
       * play nice with runtime. *)
      val dummyLock : Word32.word ref = ref 0w0
      val _ = MLton.HM.registerQueueLock (Word32.fromInt myId, dummyLock)
      val _ = MLton.Parallel.Deprecated.lockInit dummyLock

      fun communicate () =
        ( let
            val r = getRequest myId
          in
            if r = REQUEST_NONE then
              ()
            else if r = REQUEST_BLOCKED then
              die (fn _ => "scheduler bug: serve while blocked")
            else
              (* r is a friendly processor id which is requesting work *)
              ( setRequest (myId, REQUEST_NONE)
              ; case Queue.popBack myQueue of
                  NONE => setMailReject r
                | SOME (task, level) =>
                    let
                      val ch = HH.newHeap ()
                    in
                      HH.attachChild (Thread.current (), ch, level);
                      setHeapBox (r, ch);
                      setTaskBox (r, SOME task);
                      setMailReceiving r
                    end
              )
          end
        ; setHasWork (myId, not (Queue.empty myQueue))
        )

      fun push x =
        Queue.pushFront (x, myQueue)

      fun popDiscard () =
        case Queue.popFront myQueue of
          NONE => false
        | SOME _ => true

      (* ------------------------------------------------------------------- *)

      fun verifyStatus () =
        if checkHasWork myId = false then ()
        else die (fn _ => "scheduler bug: status not set correctly while idle")

      fun randomOtherId () =
        let val other = SimpleRandom.boundedInt (0, P-1) myRand
        in if other < myId then other else other+1
        end

      fun blockRequests () =
        let
          val r = getRequest myId
        in
          if r = REQUEST_NONE then
            if casRequest (myId, REQUEST_NONE, REQUEST_BLOCKED) then ()
            else blockRequests () (* recurs at most once *)
          else if r = REQUEST_BLOCKED then
            die (fn _ => "scheduler bug: attempted to block while already blocked")
          else
            ( setRequest (myId, REQUEST_BLOCKED)
            ; setMailReject r
            )
        end

      fun unblockRequests () = setRequest (myId, REQUEST_NONE)

      fun request idleTimer =
        let
          val friend = randomOtherId ()
          val hasWork = checkHasWork friend
          val available = (getRequest friend = REQUEST_NONE)
        in
          if not (available andalso hasWork andalso casRequest (friend, REQUEST_NONE, myId)) then
            (verifyStatus (); request (tickTimer idleTimer))
          else if not (waitForMail myId) then
            (* mail request rejected *)
            (verifyStatus (); request (tickTimer idleTimer))
          else
            (* mail request accepted *)
            idleTimer
        end

      (* ------------------------------------------------------------------- *)

      fun acquireWork () : unit =
        let
          val idleTimer = startTimer myId
          val _ = setHasWork (myId, false)
          val _ = blockRequests ()

          (* find work from another worker. Eventually we receive
           *   - a task to execute (taken out of the task box by the child thread)
           *   - a heap to execute it in (taken out of the heap box now)
           *)
          val idleTimer' = request idleTimer
          val hh = getHeapBox myId

          val _ = unblockRequests ()
          val _ = stopTimer idleTimer'

          val taskThread = Thread.copy prototypeThread
          val _ = HH.attachHeap (taskThread, hh)
          val _ = threadSwitch taskThread
        in
          returnFromExecute ()
        end

      and returnFromExecute () =
        case !myRetArg of
          NONE => die (fn _ => "scheduler bug: no arg when returning to scheduler")
        | SOME (incounter, cont) =>
            ( myRetArg := NONE
            ; if decrementHitsZero incounter
              then (communicate (); threadSwitch cont; returnFromExecute ())
              else acquireWork ()
            )

      fun returnToSched (c, k) =
        ( myRetArg := SOME (c, k)
        ; threadSwitch mySchedThread
        )

      (* ------------------------------------------------------------------- *)

      val _ = arrayUpdate (pushFuncs, myId, push)
      val _ = arrayUpdate (popDiscardFuncs, myId, popDiscard)
      val _ = arrayUpdate (communicateFuncs, myId, communicate)
      val _ = arrayUpdate (returnToScheds, myId, returnToSched)

      (* val _ = dbgmsg (fn _ => "sched " ^ Int.toString myId ^ " finished init") *)

    in
      if myId = 0 then returnFromExecute else acquireWork
    end

  (* ========================================================================
   * INITIALIZATION
   *)

  fun sched () =
    let val acquireWork = setupSchedLoop ()
    in acquireWork ()
    end

  val _ = MLton.Parallel.registerProcessorFunction sched
  val _ = MLton.Parallel.initializeProcessors ()

  (* Initializes scheduler-local data for proc 0, including remembering the
   * current thread as the "scheduler thread" for this worker. In order to
   * keep "user" threads separate from "scheduler" threads, we need to copy
   * the current thread and use the COPY as the main program thread, which
   * happens below. *)
  val returnFromExecute = setupSchedLoop ()

  (* This manages to hijack the "original" program thread as the scheduler
   * thread, while the copied thread is used to execute the actual program.
   * Before switching to the copy, we give the copy a hierarchical heap. *)
  val executeMain = ref false
  val _ = Thread.copyCurrent ()
  val _ =
    if !executeMain then ()
    else let
           val t = Thread.copy (Thread.savedPre ())
         in
           ( executeMain := true
           ; HH.attachHeap (t, HH.newHeap ())
           ; threadSwitch t
           ; returnFromExecute ()
           )
         end

end

structure ForkJoin :> FORK_JOIN =
struct
  open Scheduler.ForkJoin

  fun for (i, j) f = if i = j then () else (f i; for (i+1, j) f)

  fun parfor grain (i, j) f =
    let val n = j - i
    in if n <= grain
       then for (i, j) f
       else ( fork ( fn _ => parfor grain (i, i + n div 2) f
                   , fn _ => parfor grain (i + n div 2, j) f
                   )
            ; ()
            )
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
