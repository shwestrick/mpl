structure SimpleRandomSet:
sig
  type elem = int (* must be positive *)
  type t

  (* `new n` creates empty set on possible elements [0..n) *)
  val new: int -> t

  val size: t -> int

  val insert: t -> elem -> unit
  val remove: t -> elem -> unit

  (* select uniformly random element; throws exn on empty set *)
  val sample: t -> SMLNJRandom.rand -> elem

  (* select something outside the set *)
  val sampleComplement: t -> SMLNJRandom.rand -> elem
end =
struct

  type elem = int

  (* data[0..size) contains the elements of the set
   * invariant: data[idx[x]] == x
   *)
  type t = {data: elem array,
            idx: int array,
            size: int ref}

  fun new n =
    { data = Array.tabulate (n, fn i => i)
    , idx = Array.tabulate (n, fn i => i)
    , size = ref 0
    }

  fun insert ({data, idx, size}: t) x =
    let
      val i = Array.sub (idx, x)
      val sz = !size
    in
      if i < sz then
        (* already contains x *)
        ()
      else if i = sz then
        (* no need to swap, just bump size *)
        size := sz + 1
      else
        (* swap to put x at data[sz] and then bump size *)
        let
          val y = Array.sub (data, sz)
        in
          Array.update (data, sz, x);
          Array.update (data, i, y);
          Array.update (idx, x, sz);
          Array.update (idx, y, i);
          size := sz + 1
        end
    end

  fun remove ({data, idx, size}: t) x =
    let
      val i = Array.sub (idx, x)
      val sz = !size
    in
      if i >= sz then
        (* already doesn't contain x *)
        ()
      else if i = sz-1 then
        (* no need to swap, just bump size *)
        size := sz - 1
      else
        (* swap to put x at data[sz-1] and then bump size *)
        let
          val y = Array.sub (data, sz-1)
        in
          Array.update (data, sz-1, x);
          Array.update (data, i, y);
          Array.update (idx, x, sz-1);
          Array.update (idx, y, i);
          size := sz - 1
        end
    end

  fun sample ({data, idx, size}: t) rand =
    let
      val sz = !size
    in
      if sz = 0 then
        raise Fail "sample on empty set"
      else
        Array.sub (data, SMLNJRandom.randRange (0, sz-1) rand)
    end

  fun sampleComplement ({data, idx, size}: t) rand =
    let
      val sz = !size
    in
      if sz = Array.length data then
        raise Fail "sampleComplement on full set"
      else
        Array.sub (data, SMLNJRandom.randRange (sz, Array.length data - 1) rand)
    end

  fun size (set: t) = !(#size set)

end
