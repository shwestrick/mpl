structure MLtonSimd :> MLTON_SIMD =
struct
  structure Prim = Primitive.MLton.Simd
  type v8i8 = Word64.word
  fun create_v8i8 a b c d e f g h =
    Prim.create_v8i8 (a, b, c, d, e, f, g, h)

  fun to_w64 (x: v8i8) : Word64.word = x
end