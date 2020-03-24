signature TABLE =
sig
  structure Key: KEY
  type 'a t

  val size: 'a t -> int
  val toString: ('a -> string) -> 'a t -> string
  val elements: 'a t -> (Key.t * 'a) list
  val keys: 'a t -> Key.t list
  val values: 'a t -> 'a list

  (* For debugging. Verify that the table is well-formed. *)
  val check: 'a t -> bool

  val empty: 'a t
  val singleton: Key.t * 'a -> 'a t

  val map: ('a -> 'b) -> 'a t -> 'b t
  val mapk: (Key.t * 'a -> 'b) -> 'a t -> 'b t
  val filter: ('a -> bool) -> 'a t -> 'a t
  val filterk: (Key.t * 'a -> bool) -> 'a t -> 'a t
  val foldl: (Key.t * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b
  val foldr: (Key.t * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b

  val first: 'a t -> (Key.t * 'a) option
  val last: 'a t -> (Key.t * 'a) option

  val splitAt: Key.t -> 'a t -> 'a t * 'a option * 'a t
  val join: 'a t * 'a t -> 'a t
  val joinMid: 'a t * Key.t * 'a * 'a t -> 'a t

  val lookup: Key.t -> 'a t -> 'a option
  val insertWith: ('a * 'a -> 'a) -> Key.t * 'a -> 'a t -> 'a t
  val insert: Key.t * 'a -> 'a t -> 'a t
  val remove: Key.t -> 'a t -> 'a t

  val unionWith: ('a * 'a -> 'a) -> 'a t * 'a t -> 'a t
  val union: 'a t * 'a t -> 'a t
  val intersectWith: ('a * 'b -> 'c) -> 'a t * 'b t -> 'c t
  val intersect: 'a t * 'a t -> 'a t
  val difference: 'a t * 'b t -> 'a t
end
