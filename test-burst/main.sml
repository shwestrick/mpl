fun sfib n =
  if n <= 1 then n else sfib (n-1) + sfib (n-2)

fun fib n =
  if n <= 20 then sfib n
  else
    let
      val (x,y) = ForkJoin.par (fn _ => fib (n-1), fn _ => fib (n-2))
    in
      x + y
    end

val (bursts, sn, pn) =
  case List.map Int.fromString (CommandLine.arguments ()) of
    [bursts, n, m] => (valOf bursts, valOf n, valOf m)
  | _ => raise Fail "args"

val _ = print ("bursts " ^ Int.toString bursts ^ "\n")
val _ = print ("seq_n  " ^ Int.toString sn ^ "\n")
val _ = print ("par_n  " ^ Int.toString pn ^ "\n")

val t0 = Time.now ()
val result =
  Vector.tabulate (2*bursts+1, fn i =>
    if i mod 2 = 0 then sfib sn else fib pn)
val t1 = Time.now ()

val _ = print ("finished in " ^ Time.fmt 4 (Time.- (t1, t0)) ^ "s\n")
val _ = print ("results " ^ Int.toString (Vector.sub (result, 0)) ^ " " ^ Int.toString (Vector.sub (result, 1)) ^ "\n")
