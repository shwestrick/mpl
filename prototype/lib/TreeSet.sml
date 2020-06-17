functor TreeSet (Key: KEY):
sig
  type t
  val empty: t
  val size: t -> int
  val insert: Key.t -> t -> t
  val remove: Key.t -> t -> t
  val member: Key.t -> t -> bool
  val union: t * t -> t

  val fromList: Key.t list -> t
  val equal: t * t -> bool
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

  fun fromList ks =
    List.foldr (fn (x, s) => insert x s) empty ks

  fun equal (s1, s2) = T.equal (fn _ => true) (s1, s2)

  fun union (s1, s2) = T.union (s1, s2)

end
