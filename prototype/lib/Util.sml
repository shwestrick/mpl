structure Util =
struct

  fun zipWith f xs ys =
    case (xs, ys) of
      ([], _) => []
    | (_, []) => []
    | (x :: xs', y :: ys') => f x y :: zipWith f xs' ys'

  fun allTrue xs = List.all (fn b => b) xs

end
