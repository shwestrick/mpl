(* Lang0 has no types. Just raw AST *)
structure Lang0 =
struct

  structure Id = Identifier
  type var = Id.t
  (* type typ = Type.t *)

  datatype exp =
    Var of var
  | App of exp * exp
  | Par of exp * exp
  | Fst of exp
  | Snd of exp
  | Let of var * exp * exp
  | Func of var * var * exp (* function name, argument, function body *)
  | Num of int
  | IfZero of exp * exp * exp
  | Op of string * (int * int -> int) * exp * exp

  fun OpAdd (e1, e2) = Op ("+", op+, e1, e2)
  fun OpSub (e1, e2) = Op ("-", op-, e1, e2)
  fun OpMul (e1, e2) = Op ("*", op*, e1, e2)

  fun parens s = "(" ^ s ^ ")"

  fun toString e =
    case e of
      Var v => Id.toString v
    | Num n => Int.toString n
    | App (e1, e2) =>
        toStringP e1 ^ " " ^ toStringP e2
    | Par (e1, e2) =>
        toStringP e1 ^ " || " ^ toStringP e2
    | Fst e' => "fst " ^ toStringP e'
    | Snd e' => "snd " ^ toStringP e'
    | Let (v, e1, e2) =>
        "let " ^ Id.toString v ^ " = " ^ toString e1 ^ " in " ^ toString e2
    | Func (func, arg, body) =>
        "fun " ^ Id.toString func ^ " " ^ Id.toString arg ^ " is " ^ toString body
    | Op (name, _, e1, e2) =>
        toStringP e1 ^ " " ^ name ^ " " ^ toStringP e2
    | IfZero (e1, e2, e3) =>
        "ifz " ^ toString e1 ^ " then " ^ toString e2 ^ " else " ^ toString e3

  and toStringP e =
    let
      val needsP =
        case e of
          App _ => true
        | Par _ => true
        | Op _ => true
        | IfZero _ => true
        | Fst _ => true
        | Snd _ => true
        | Let _ => true
        | Func _ => true
        | _ => false
    in
      if needsP then parens (toString e) else toString e
    end

  fun canStep e =
    case e of
      Op _ => true
    | App _ => true
    | Par (e1, e2) => canStep e1 orelse canStep e2
    | IfZero _ => true
    | Fst _ => true
    | Snd _ => true
    | Let _ => true
    | _ => false

  fun deFunc e = case e of Func x => x | _ => raise Fail "deFunc"
  fun deNum e = case e of Num x => x | _ => raise Fail "deNum"

  (* substitute [e'/x]e *)
  fun subst (e', x) e =
    let
      (* val _ = print ("[" ^ toString e' ^ " / " ^ Id.toString x ^ "]" ^ toString e ^ "\n") *)
      val doit = subst (e', x)
    in
      case e of
        Var v => if Id.eq (v, x) then e' else Var v
      | App (e1, e2) => App (doit e1, doit e2)
      | Par (e1, e2) => Par (doit e1, doit e2)
      | Fst e' => Fst (doit e')
      | Snd e' => Snd (doit e')
      | Let (v, e1, e2) => Let (v, doit e1, doit e2)
      | Func (func, arg, body) => Func (func, arg, doit body)
      | Num n => Num n
      | Op (name, f, e1, e2) => Op (name, f, doit e1, doit e2)
      | IfZero (e1, e2, e3) => IfZero (doit e1, doit e2, doit e3)
    end

  fun tryStep (e: exp): exp =
    case e of
      App (e1, e2) =>
        if canStep e1 then
          App (tryStep e1, e2)
        else if canStep e2 then
          App (e1, tryStep e2)
        else
          let
            val (func, arg, body) = deFunc e1
          in
            subst (e1, func) (subst (e2, arg) body)
          end

    | Par (e1, e2) =>
        if canStep e1 then
          Par (tryStep e1, e2)
        else if canStep e2 then
          Par (e1, tryStep e2)
        else
          raise Fail "tryStep Par"

    | Fst e' =>
        if canStep e' then
          Fst (tryStep e')
        else
          (case e' of
             Par (a, _) => a
           | _ => raise Fail "tryStep Fst")

    | Snd e' =>
        if canStep e' then
          Snd (tryStep e')
        else
          (case e' of
             Par (_, b) => b
           | _ => raise Fail "tryStep Snd")

    | Let (v, e1, e2) =>
        if canStep e1 then
          Let (v, tryStep e1, e2)
        else
          subst (e1, v) e2

    | Op (name, f, e1, e2) =>
        if canStep e1 then
          Op (name, f, tryStep e1, e2)
        else if canStep e2 then
          Op (name, f, e1, tryStep e2)
        else
          let
            val n1 = deNum e1
            val n2 = deNum e2
          in
            Num (f (n1, n2))
          end

    | IfZero (e1, e2, e3) =>
        if canStep e1 then
          IfZero (tryStep e1, e2, e3)
        else
          let
            val n = deNum e1
          in
            if n = 0 then e2 else e3
          end

    | _ => raise Fail "tryStep"

  fun step e =
    if canStep e then SOME (tryStep e) else NONE

  fun exec e =
    let
      val _ = print (toString e ^ "\n")
    in
      case step e of
        NONE => print "DONE\n"
      | SOME e' => exec e'
    end

  val fact: exp =
    let
      val f = Id.new "fact"
      val n = Id.new "n"
      val body =
        IfZero (Var n, Num 1, OpMul (Var n, App (Var f, OpSub (Var n, Num 1))))
    in
      Func (f, n, body)
    end

  val doubleFirst: exp =
    let
      val f = Id.new "f"
      val x = Id.new "x"
      val y = Id.new "y"
    in
      Func (f, x, Let (y, Fst (Var x), OpAdd (Var y, Var y)))
    end

  val doesntTypeCheck: exp =
    let
      val f = Id.new "f"
      val x = Id.new "x"
      val ff = Id.new "ff"
      val idFunc =
        Func (f, x, Var x)
    in
      (* make f the identity function, but apply it to two different
       * arguments. we don't have polymorphism! *)
      Let (ff, idFunc, Par (App (Var ff, Num 1), App (Var ff, (Par (Num 2, Num 3)))))
    end

  val parAdd: exp =
    let
      val left = OpAdd (Num 1, Num 2)
      val right = OpAdd (Num 3, Num 4)
      val x = Id.new "x"
    in
      Let (x, Par (left, right), OpAdd (Fst (Var x), Snd (Var x)))
    end

end
