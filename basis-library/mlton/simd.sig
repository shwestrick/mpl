signature MLTON_SIMD =
sig
  type v8i8
  val create_v8i8: Word8.word -> Word8.word -> Word8.word -> Word8.word -> Word8.word -> Word8.word -> Word8.word -> Word8.word -> v8i8
  val to_w64: v8i8 -> Word64.word
end