structure MultiMailbox :>
sig
  type elem = int
  type t

  val new: int -> t
  val insert: t -> elem -> bool
  val size: t -> int
  val removeContents: t -> elem list
  val freeze: t -> unit
  val thaw: t -> unit
end =
struct

  fun casRef r (old, new) =
    (MLton.Parallel.compareAndSwap r (old, new) = old)

  type elem = int
  type t = elem array * int ref

  fun new capacity =
    (Array.tabulate (capacity, fn _ => ~1), ref 0)

  fun invalidElem x = x < 0

  fun insert (slots, next) x =
    if invalidElem x then raise Fail "invalid mailbox element" else
    let
      val i = !next
    in
      if i < 0 orelse i >= Array.length slots then
        false
      else if casRef next (i, i+1) then
        (Array.update (slots, i, x); true)
      else
        insert (slots, next) x
    end

  fun size (_, next) =
    let
      val r = !next
    in
      if r < 0 then ~(r+1) else r
    end

  fun toggle (slots, next) =
    let
      val i = !next
    in
      if casRef next (i, ~i - 1) then
        ()
      else
        toggle (slots, next)
    end

  fun removeContents (mm as (slots, next)) =
    if !next >= 0 then raise Fail "cannot remove contents of unfrozen mailbox" else
    let
      val n = size mm

      fun takeLoop acc i =
        if i >= n then acc else
        let
          val x = Array.sub (slots, i)
        in
          if invalidElem x then
            takeLoop acc i
          else
            (Array.update (slots, i, ~1); takeLoop (x :: acc) (i+1))
        end

      val result = takeLoop [] 0
    in
      next := ~1; (* frozen, but empty *)
      result
    end

  fun freeze (slots, next) =
    if !next < 0 then
      raise Fail "freeze on already frozen mailbox"
    else
      toggle (slots, next)

  fun thaw (slots, next) =
    if !next >= 0 then
      raise Fail "thaw on unfrozen mailbox"
    else
      toggle (slots, next)

end
