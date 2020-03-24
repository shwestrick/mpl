functor TreeSet (Key: KEY):
sig
  type t
  val empty: t
  val size: t -> int
  val insert: Key.t -> t -> t
  val remove: Key.t -> t -> t
  val member: Key.t -> t -> bool
end =
struct

  structure T = TreeTable (Key)

  type t = unit T.t

  val empty = T.empty
  val size = T.size

  fun insert x s = T.insert (x, ()) s

  fun remove x s = T.remove x s

  fun member x s =
    case T.lookup x s of
      NONE => false
    | SOME _ => true

end
