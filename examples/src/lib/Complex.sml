(* the complex numbers *)
structure Complex:
sig
  type t
  val fromReal: real -> t
  val zero: t
  val one: t
  val i: t
  val mul: t * t -> t
  val add: t * t -> t
  val sub: t * t -> t
  val expi: real -> t (* exp(i*x) *)
  val toString: t -> string
  val magnitude: t -> real
end =
struct
  (* real and imaginary parts *)
  type t = real * real
  fun fromReal x = (x, 0.0)
  val zero = fromReal 0.0
  val one = fromReal 1.0
  val i = (0.0, 1.0)
  fun add ((x1, y1): t, (x2, y2)) = (x1+x2, y1+y2)
  fun sub ((x1, y1): t, (x2, y2)) = (x1-x2, y1-y2)
  fun mul ((x1, y1): t, (x2, y2)) = (x1*x2 - y1*y2, x1*y2 + x2*y1)
  fun expi x = (Math.cos x, Math.sin x)
  fun toString (x, y) =
    case (Real.== (x, 0.0), Real.== (y, 0.0)) of
      (true, true) => "0"
    | (true, false) => Real.toString y ^ "i"
    | (false, true) => Real.toString x
    | (false, false) => Real.toString x ^ "+" ^ Real.toString y ^ "i"

  fun magnitude (x, y) = Math.sqrt (x*x + y*y)
end
