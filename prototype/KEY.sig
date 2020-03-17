signature KEY =
sig
  type t
  val compare: t * t -> order
  val hash: t -> int
  val toString: t -> string
end
