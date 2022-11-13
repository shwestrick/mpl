functor S3 (val scaleUpFactor: int):
sig
  val incrSurplus: SMLNJRandom.rand -> int -> unit
  val decrSurplus: int -> unit
  val incrStealing: int -> unit
  val decrStealing: SMLNJRandom.rand -> int -> unit
  val trySleep: int -> unit
end =
struct

  val numProcs = MLton.Parallel.numberOfProcessors
  val procNum = MLton.Parallel.processorNumber

  fun casRef r (old, new) =
    MLton.eq (MLton.Parallel.compareAndSwap r (old, new), old)

  fun casArray (a, i) (old, new) =
    MLton.eq (MLton.Parallel.arrayCompareAndSwap (a, i) (old, new), old)


  fun die strfn =
    ( print (Int.toString (myWorkerId ()) ^ ": " ^ strfn ())
    ; OS.Process.exit OS.Process.failure
    )
    
  (* ===================================================================== *)
  
  structure C:
  sig
    type t
    datatype stuff = Stuff of {sleepers: int, stealers: int, surplus: int}
    val pack: stuff -> t
    val unpack: t -> stuff
  end =
  struct
    type t = Word64.word
    datatype view = Stuff of {sleepers: int, stealers: int, surplus: int}

    (* `shift` is the number of bits per component. If you change the
     * value of `shift`, then everything else is recomputed automatically.
     * Requires 3*shift <= word size.
     * (Here, we're using 64-bit words)
     *)
    val shift = 0w20

    (* automatically computed based on the shift *)
    val ulimit = Word64.toInt (Word64.<< (0w1, shift))
    val slimit = Word64.toInt (Word64.>> (Word64.<< (0w1, shift), 0w1))
    val mask = Word64.- (Word64.<< (0w1, shift), 0w1)

    (* Negative values of a component are allowed. These functions will
     * correctly pack and unpack via twos complement.
     *)
    fun packOne (component: int) : Word64.word =
      Word64.andb (Word64.fromInt component, mask)

    fun unpackOne (packedComponent: Word64.word) : int =
      let
        val v = Word64.toInt packedComponent
      in
        if v < slimit then
          v
        else
          v - ulimit
      end

    fun pack (Stuff {sleepers, stealers, surplus}) =
      let
        val v = packOne sleepers
        val v = Word64.orb (Word64.<< (v, shift), packOne stealers)
        val v = Word64.orb (Word64.<< (v, shift), packOne surplus)
      in
        v
      end

    fun unpack v =
      let
        val surplus = unpackOne (Word64.andb (v, mask))
        val v = Word64.>> (v, shift)
        val stealers = unpackOne (Word64.andb (v, mask))
        val v = Word64.>> (v, shift)
        val sleepers = unpackOne (Word64.andb (v, mask))
      in
        Stuff {sleepers=sleepers, stealers=stealers, surplus=surplus}
      end
  end

  (* ===================================================================== *)


  val flags: bool array = Array.array (numProcs, false)
  val globalCounter = ref (C.pack (C.Stuff {sleepers=0, stealers=0, surplus=0}))


  fun updateCounter (f: C.stuff -> C.stuff) =
    let
      val old = !globalCounter
      val new = C.pack (f (C.unpack old))
    in
      if casRef globalCounter (old, new) then
        new
      else
        updateCounter f
    end
  

  fun needsSentinel {sleepers, stealers, surplus} =
    surplus > 0 andalso stealers = 0 andalso sleepers > 0


  fun tryWake p =
    if Array.sub (flags, p) andalso casArray (flags, p) (true, false) then
      (MLton.Parallel.semPost p; true)
    else
      false


  fun incrSurplus seed p =
    let
      fun restoreInvariant stuff =
        if not (needsSentinel stuff) then
          ()
        else if tryWake (randomOther seed p) then
          ()
        else
          restoreInvariant (!globalCounter)
      
      val new = updateCounter (fn {sleepers, stealers, surplus} =>
        { sleepers = sleepers
        , stealers = stealers
        , surplus = surplus+1
        })
    in
      restoreInvariant new
    end

  
  fun decrStealing seed p =
    let
      fun restoreInvariantAndScaleUp awoken stuff =
        if not (needsSentinel stuff) andalso awoken >= scaleUpFactor then
          ()
        else if #sleepers stuff = 0 then
          ()
        else if tryWake (randomOther seed p) then
          restoreInvariantAndScaleUp (awoken+1) (!globalCounter)
        else
          restoreInvariantAndScaleUp awoken (!globalCounter)
      
      val new = updateCounter (fn {sleepers, stealers, surplus} =>
        { sleepers = sleepers
        , stealers = stealers-1
        , surplus = surplus
        })
    in
      restoreInvariantAndScaleUp 0 new
    end

  
  fun trySleep p =
    let
      val _ = Array.update (flags, p, true)
      val new = updateCounter (fn {sleepers, stealers, surplus} =>
        { sleepers = sleepers+1
        , stealers = stealers-1
        , surplus = surplus
        })

      fun sleep () = MLton.Parallel.semWait p
    in
      if not (needsSentinel new) then 
        (* No need for sentinel, so I can go to sleep *)
        sleep ()
      else if tryWake p then
        (* We need a sentinel, and I succeeded in "waking myself up", so
         * don't actually go to sleep. *)
        ()
      else
        (* We need a sentinel, but someone else has already decided to wake me
         * up, so I just need to wait for that signal to arrive.
         *)
        sleep ();

      updateCounter (fn {sleepers, stealers, surplus} =>
        { sleepers = sleepers-1
        , stealers = stealers+1
        , surplus = surplus
        });

      ()
    end


  fun decrSurplus _ =
    updateCounter (fn {sleepers, stealers, surplus} =>
      { sleepers = sleepers
      , stealers = stealers
      , surplus = surplus-1
      })


  fun incrStealing _ =
    updateCounter (fn {sleepers, stealers, surplus} =>
      { sleepers = sleepers
      , stealers = stealers+1
      , surplus = surplus
      })

end