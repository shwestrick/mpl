structure IntKey =
struct
  type t = int
  val compare = Int.compare
  val hash = Hash.hash
  val toString = Int.toString
end
