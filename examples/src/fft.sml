
val ** = Complex.mul
val ++ = Complex.add
val -- = Complex.sub

infix 7 **
infix 6 ++ --

(* Implementation based on the description given by JaJa *)
fun dft (input: real Seq.t) =
  let
    val N = Util.boundPow2 (Seq.length input)

    (*
    exp(j 2 pi f t)
     *)

    (* precompute all powers of w = e^(i 2pi/N) *)
    val w = Complex.expi (2.0 * Math.pi / Real.fromInt N)
    val wpows = SeqBasis.scan 2048 op** Complex.one (0, N) (fn i => w)
    fun wpow i = Array.sub (wpows, i)

    (* fft on the vector x, assume power-of-two length *)
    fun fft x =
      if Seq.length x = 1 then
        x
      else if Seq.length x = 2 then
        Seq.fromList [Seq.nth x 0 ++ Seq.nth x 1, Seq.nth x 0 -- Seq.nth x 1]
      else
        let
          val n = Seq.length x
          val half = n div 2

          fun u i = Seq.nth x i ++ Seq.nth x (half + i)
          fun v i = wpow i ** (Seq.nth x i -- Seq.nth x (half + i))

          fun left () = fft (Seq.tabulate u half)
          fun right () = fft (Seq.tabulate v half)

          val (z1, z2) =
            if n <= 1000
            then (left (), right ())
            else ForkJoin.par (left, right)

          fun y i =
            if Util.even i
            then Seq.nth z1 (i div 2)
            else Seq.nth z2 ((i-1) div 2)
        in
          Seq.tabulate y n
        end

    val padded =
      Seq.tabulate
        (fn i => if i < Seq.length input
                 then Complex.fromReal (Seq.nth input i)
                 else Complex.zero)
        N

    val result = fft padded
  in
    Seq.subseq result (0, Seq.length input)
  end

val numSamples = CommandLineArgs.parseInt "N" 1000000

val sampleRate = 10000.0
val fA  = 440.0
val fCs = 550.0
val fE  = 660.0

val duration = Real.fromInt numSamples / sampleRate

fun sinusoid amp freq i =
  amp * Math.cos (2.0 * Math.pi * freq * (Real.fromInt i / sampleRate))

fun hannWindow i =
  let val s = Math.sin (Math.pi * Real.fromInt i / Real.fromInt numSamples)
  in s * s
  end

val signal =
  Seq.tabulate
    (fn i =>
      hannWindow i * ( sinusoid 0.75 fA i (*
                     + sinusoid 0.5 fCs i
                     + sinusoid 0.25 fE i *)
                     ))
    numSamples

val _ = print ("fft " ^ Int.toString numSamples ^ "\n")

val t0 = Time.now ()
val result = dft signal
val t1 = Time.now ()

val _ = print ("finished in " ^ Time.fmt 4 (Time.- (t1, t0)) ^ "s\n")

(* val _ = print ("result " ^ Int.toString result ^ "\n") *)

(* frequency resolution *)
(* val df = sampleRate / Real.fromInt numSamples
val iA1 = Real.floor (fA / df)
val iA2 = Real.ceil (fA / df)

val _ = print (Real.toString (Complex.magnitude (Seq.nth result iA1)) ^ "\n")
val _ = print (Real.toString (Complex.magnitude (Seq.nth result iA2)) ^ "\n") *)

fun rtos x =
  if x < 0.0 then "-" ^ rtos (~x) else Real.fmt (StringCvt.FIX (SOME 3)) x

fun dump i =
  if i >= Seq.length signal then
    ()
  else
    (* (print (rtos (Seq.nth signal i) ^ "\n"); *)
    (print (rtos (Complex.magnitude (Seq.nth result i)) ^ "\n");
    dump (i+1))

val _ = dump 0
