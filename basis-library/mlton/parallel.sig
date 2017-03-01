(* Copyright (C) 2017 Ram Raghunathan.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature MLTON_PARALLEL =
  sig
    (**
     * Deprecated functions. Using these functions will print out a warning
     * message that they may be removed in a future release.
     *)
    structure Deprecated:
              sig
                (**
                 * Yields to the runtime
                 *)
                val yield: unit -> unit

                (**
                 * Initializes a lock to the "unlocked" state
                 *)
                val lockInit: Word32.word ref -> unit;

                (**
                 * Locks the lock.
                 *
                 * @attention Does not support recursive locking or any kind of
                 * deadlock detection!
                 *)
                val takeLock: Word32.word ref -> unit;

                (**
                 * Unlocks the locks
                 *
                 * @attantion Does not enforce that the locking thread has to be
                 * the unlocker!
                 *)
                val releaseLock: Word32.word ref -> unit;
              end

    (*
     * RAM_NOTE: Perhaps some of these should be in module-specific Unsafe
     * structures?
     *)
    structure Unsafe:
              sig
                (**
                 * Forces creation of a runtime thread object from a
                 * MLton.Thread.
                 *
                 * @note See initPrimitive in thread.sml for more information.
                 *)
                val initPrimitiveThread:
                    unit MLtonThread.t -> MLtonThread.Runnable.t

                (**
                 * Creates an uninitialized array of given size.
                 *)
                val arrayUninit: int -> 'a Array.array
              end

    exception Return

    (**
     * The number of processors available in the system
     *)
    val numberOfProcessors: int

    (**
     * Returns the processor number of the caller.
     *
     * @return The processor number, which is zero-based.
     *)
    val processorNumber: unit -> int

    (**
     * Registers a function for the non-primary processors to run.
     *
     * @param The function for them to run. While it is typed as a unit -> unit,
     * it should not ever return. Doing so raises Return.
     *)
    val registerProcessorFunction: (unit -> unit) -> unit

    (**
     * Initializes the non-primary processors.
     *
     * @attention: You <em>must</em> register a processor function with
     * registerProcessorFunction before calling this function!
     *)
    val initializeProcessors: unit -> unit;
  end