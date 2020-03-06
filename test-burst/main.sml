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
val results =
  Vector.tabulate (2*bursts+1, fn i =>
    let
      val t0 = Time.now ()
      val result = if i mod 2 = 0 then sfib sn else fib pn
      val t1 = Time.now ()
    in
      (result, Time.toReal (Time.- (t1, t0)))
    end)
val t1 = Time.now ()

val _ = print ("finished in " ^ Time.fmt 4 (Time.- (t1, t0)) ^ "s\n")
val _ = print ("results " ^ Int.toString (#1 (Vector.sub (results, 0))) ^ " " ^ Int.toString (#1 (Vector.sub (results, 1))) ^ "\n")

val seqTimes = List.tabulate (bursts+1, fn i =>
  let
    val (_, t) = Vector.sub (results, 2*i)
  in
    t
  end)
val seqTotal = List.foldl op+ 0.0 seqTimes
val seqAvg = seqTotal / Real.fromInt (bursts+1)
val _ = print ("seq_avg " ^ Real.toString seqAvg ^ "\n")

val parTimes = List.tabulate (bursts, fn i =>
  let
    val (_, t) = Vector.sub (results, 2*i+1)
  in
    t
  end)
val parTotal = List.foldl op+ 0.0 parTimes
val parAvg = parTotal / Real.fromInt bursts
val _ = print ("par_avg " ^ Real.toString parAvg ^ "\n")
