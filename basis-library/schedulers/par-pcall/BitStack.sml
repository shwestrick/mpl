structure BitStack :>
sig
  type t
  datatype bit = Zero | One
  val empty: t
  val push: bit * t -> t
  val pop: t -> bit * t
  val size: t -> int
end =
struct
  
  datatype t =
    T of {front: Word64.word, front_size: int, rest: Word64.word list}


  datatype bit = Zero | One


  val empty = T {front = 0w0, front_size = 0, rest = []}


  fun bit_to_word b =
    case b of
      Zero => 0w0: Word64.word
    | One => 0w1

  
  fun word_to_bit (w: Word64.word) =
    if w = 0w0 then Zero else One


  fun push (b, T {front, front_size, rest}) =
    if front_size < 64 then
      T { front = Word64.orb (Word64.<< (front, 0w1), bit_to_word b)
        , front_size = front_size + 1
        , rest = rest
        }
    else
      T {front = bit_to_word b, front_size = 1, rest = front :: rest}


  fun pop (T {front, front_size, rest}) =
    if front_size > 0 then
      ( word_to_bit (Word64.andb (front, 0w1))
      , T { front = Word64.>> (front, 0w1)
          , front_size = front_size - 1
          , rest = rest
          }
      )
    else
      pop (T {front = List.hd rest, front_size = 64, rest = List.tl rest})

  
  fun size (T {front_size, rest, ...}) =
    List.length rest * 64 + front_size

end