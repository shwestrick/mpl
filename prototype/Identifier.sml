structure Identifier:
sig
  type t
  val toString: t -> string
  val new: string -> t
  val renew: t -> t
  val eq: t * t -> bool
  val compare: t * t -> order
  val hash: t -> int

  val var: unit -> t
  val stamp: unit -> t
  val stampVar: unit -> t
end =
struct
  type t = string * int

  val counter = ref 0

  fun new name =
    let
      val c = !counter
    in
      counter := c + 1;
      (name, c)
    end

  fun renew (name, _) = new name

  fun toString (name, c) = name ^ "_" ^ Int.toString c

  fun eq ((_, c1), (_, c2)) = c1 = c2

  fun compare ((_, c1), (_, c2)) = Int.compare (c1, c2)
  fun hash (_, c) = Hash.hash c

  fun var () = new "x"
  fun stamp () = new "d"
  fun stampVar () = new "a"
end
