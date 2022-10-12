functor MkStack(type elem):
sig
  type elem = elem
  type t

  val new: unit -> t
  val push: elem * t -> unit
  val pop: t -> elem option

  val popOldest: t -> elem option
  val peekOldest: t -> elem option

  val currentSize: t -> int

  val register: MLton.Thread.Basic.t * t -> unit
  val current: MLton.Thread.Basic.t -> t option

  val same: t * t -> bool
end =
struct

  type elem = elem

  val updNB = MLton.HM.arrayUpdateNoBarrier
  val subNB = MLton.HM.arraySubNoBarrier

  datatype t =
    T of {start: int ref, stop: int ref, data: elem option array}

  fun new () =
    T { start = ref 0
      , stop = ref 0
      , data = Array.array (100, NONE)
      }

  val dummy = ref (new ())

  fun register (thread, j) =
    MLton.Thread.HierarchicalHeap.registerJStack (thread, ref j)

  fun current thread : t option =
    case MLton.Thread.HierarchicalHeap.currentJStack (thread, dummy) of
      NONE => NONE
    | SOME r => SOME (!r)


  fun same (T j1, T j2) =
    #start j1 = #start j2 andalso
    #stop j1 = #stop j2 andalso
    #data j1 = #data j2


  fun push (x, T {start, stop, data}) =
    let
      val i = !stop
    in
      updNB (data, i, SOME x);
      stop := i + 1
    end


  fun pop (T {start, stop, data}) =
    let
      val i = !start
      val j = !stop
    in
      if i >= j then NONE else
      let
        val result = subNB (data, j-1)
      in
        updNB (data, j-1, NONE);
        stop := j-1;
        if i >= j-1 then (start := 0; stop := 0) else ();
        result
      end
    end

  fun popOldest (T {start, stop, data}) =
    let
      val i = !start
      val j = !stop
    in
      if i >= j then NONE else
      let
        val result = subNB (data, i)
      in
        updNB (data, i, NONE);
        start := i+1;
        if i+1 >= j then (start := 0; stop := 0) else ();
        result
      end
    end

  fun peekOldest (T {start, stop, data}) =
    let
      val i = !start
      val j = !stop
    in
      if i >= j then NONE else subNB (data, i)
    end

  fun currentSize (T {start, stop, ...}) =
    !stop - !start

end
