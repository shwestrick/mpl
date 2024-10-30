structure DePa:
sig
  type t
  val init: t
  val fork: t -> t * t
  val join: t * t -> t
end =
struct
  
  datatype t = T of {path: BitStack.t, depth: int}

  val init = T {path = BitStack.empty, depth = 0}

  fun fork (T {path, depth}) =
    ( T {path = BitStack.push (BitStack.Zero, path), depth = depth+1}
    , T {path = BitStack.push (BitStack.One, path), depth = depth+1}
    )

  fun join (T {path=p1, depth=d1}, T {path=p2, depth=d2}) =
    let
      val (_, p) = BitStack.pop p1
    in
      T {path = p, depth = 1 + Int.max (d1, d2)}
    end

end