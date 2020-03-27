(* Lang0 has no types. Just raw AST *)
structure Lang0 =
struct

  structure Id = Identifier
  structure IdTable = TreeTable(Id)
  type var = Id.t
  (* type typ = Type.t *)

  type loc = Id.t

  datatype exp =
    Var of var
  | Loc of loc (* "internal"; not visible to Langs 1 and 2 *)
  | Ref of exp
  | Upd of exp * exp
  | Bang of exp
  | Seq of exp * exp
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
    | Loc l => Id.toString l
    | Ref e' => "ref " ^ toStringP e'
    | Bang e' => "!" ^ toStringP e'
    | Upd (e1, e2) => toStringP e1 ^ " := " ^ toStringP e2
    | App (e1, e2) =>
        toStringP e1 ^ " " ^ toStringP e2
    | Seq (e1, e2) =>
        toStringP e1 ^ " ; " ^ toStringP e2
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
        | Upd _ => true
        | Bang _ => true
        | Seq _ => true
        | _ => false
    in
      if needsP then parens (toString e) else toString e
    end

  fun deFunc e = case e of Func x => x | _ => raise Fail "deFunc"
  fun deNum e = case e of Num x => x | _ => raise Fail "deNum"
  fun deLoc e = case e of Loc l => l | _ => raise Fail "deLoc"
  fun dePar e = case e of Par x => x | _ => raise Fail "dePar"
  fun deRef e = case e of Ref x => x | _ => raise Fail "deRef"

  (* substitute [e'/x]e *)
  fun subst (e', x) e =
    let
      (* val _ = print ("[" ^ toString e' ^ " / " ^ Id.toString x ^ "]" ^ toString e ^ "\n") *)
      val doit = subst (e', x)
    in
      case e of
        Var v => if Id.eq (v, x) then e' else Var v
      | Num n => Num n
      | Loc l => Loc l
      | Ref e' => Ref (doit e')
      | Upd (e1, e2) => Upd (doit e1, doit e2)
      | Bang e' => Bang (doit e')
      | App (e1, e2) => App (doit e1, doit e2)
      | Par (e1, e2) => Par (doit e1, doit e2)
      | Seq (e1, e2) => Seq (doit e1, doit e2)
      | Fst e' => Fst (doit e')
      | Snd e' => Snd (doit e')
      | Let (v, e1, e2) => Let (v, doit e1, doit e2)
      | Func (func, arg, body) => Func (func, arg, doit body)
      | Op (name, f, e1, e2) => Op (name, f, doit e1, doit e2)
      | IfZero (e1, e2, e3) => IfZero (doit e1, doit e2, doit e3)
    end

  (* mapping of locations to expressions *)
  type memory = exp IdTable.t

  fun getLoc loc mem =
    case IdTable.lookup loc mem of
      NONE => raise Fail ("getLoc " ^ Id.toString loc)
    | SOME x => x

  fun step (m, e) =
    case e of
      Num x    => NONE
    | Loc x    => NONE
    | App x    => SOME (stepApp m x)
    | Par x    => SOME (stepPar m x)
    | Fst x    => SOME (stepFst m x)
    | Snd x    => SOME (stepSnd m x)
    | Let x    => SOME (stepLet m x)
    | Op x     => SOME (stepOp m x)
    | IfZero x => SOME (stepIfZero m x)
    | Func x   => SOME (stepFunc m x)
    | Ref x    => SOME (stepRef m x)
    | Bang x   => SOME (stepBang m x)
    | Upd x    => SOME (stepUpd m x)
    | Seq x    => SOME (stepSeq m x)

  and stepApp m (e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', App (e1', e2))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', App (e1, e2'))
        | NONE =>
            let
              val (func, arg, body) = deFunc (getLoc (deLoc e1) m)
            in
              (m, subst (e1, func) (subst (e2, arg) body))
            end

  and stepPar m (e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', Par (e1', e2))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', Par (e1, e2'))
        | NONE =>
            let
              val l = Id.loc ()
            in
              (IdTable.insert (l, Par (e1, e2)) m, Loc l)
            end

  and stepFst m e =
    case step (m, e) of
      SOME (m', e') => (m', Fst e')
    | NONE =>
        (m, #1 (dePar (getLoc (deLoc e) m)))

  and stepSnd m e =
    case step (m, e) of
      SOME (m', e') => (m', Snd e')
    | NONE =>
        (m, #2 (dePar (getLoc (deLoc e) m)))

  and stepLet m (v, e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', Let (v, e1', e2))
    | NONE => (m, subst (e1, v) e2)

  and stepOp m (name, oper, e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', Op (name, oper, e1', e2))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', Op (name, oper, e1, e2'))
        | NONE =>
            let
              val n1 = deNum e1
              val n2 = deNum e2
            in
              (m, Num (oper (n1, n2)))
            end

  and stepIfZero m (e1, e2, e3) =
    case step (m, e1) of
      SOME (m', e1') => (m', IfZero (e1', e2, e3))
    | NONE =>
        if deNum e1 = 0 then (m, e2) else (m, e3)

  and stepFunc m (func, arg, body) =
    let
      val l = Id.loc ()
    in
      (IdTable.insert (l, Func (func, arg, body)) m, Loc l)
    end

  and stepRef m e =
    case step (m, e) of
      SOME (m', e') => (m', Ref e')
    | NONE =>
        let
          val l = Id.loc ()
        in
          (IdTable.insert (l, Ref e) m, Loc l)
        end

  and stepBang m e =
    case step (m, e) of
      SOME (m', e') => (m', Bang e')
    | NONE =>
        (m, deRef (getLoc (deLoc e) m))

  and stepUpd m (e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', Upd (e1', e2))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', Upd (e1, e2'))
        | NONE =>
            (IdTable.insert (deLoc e1, Ref e2) m, e2)

  and stepSeq m (e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', Seq (e1', e2))
    | NONE => (m, e2)

  fun exec e =
    let
      fun loop (m, e) =
        let
          val _ = print (IdTable.toString (fn e => " " ^ toString e ^ "\n") m ^ "\n")
          val _ = print (toString e ^ "\n\n")
        in
          case step (m, e) of
            NONE => (m, e)
          | SOME (m', e') => loop (m', e')
        end

      val (m, e) = loop (IdTable.empty, e)
    in
      case e of
        Loc l => print ("RESULT: " ^ toString (getLoc l m) ^ "\n")
      | Num n => print ("RESULT: " ^ Int.toString n ^ "\n")
      | _ => print ("ERROR\n");

      (m, e)
    end

  (* ======================================================================= *)

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

  val iterFib: exp =
    let
      (* iterFib takes x = ((a, b), n) where a and b are the two most recent *)
      val iterFib = Id.new "iterFib"
      val x = Id.new "x"
      val a = Fst (Fst (Var x))
      val b = Snd (Fst (Var x))
      val n = Snd (Var x)
      val elseBranch =
        App (Var iterFib, Par (Par (b, OpAdd (a, b)), OpSub (n, Num 1)))
      val body = IfZero (n, a, elseBranch)
    in
      Func (iterFib, x, body)
    end

  val fib: exp =
    let
      val fib = Id.new "fib"
      val n = Id.new "n"
    in
      Func (fib, n, App (iterFib, Par (Par (Num 0, Num 1), Var n)))
    end

  val impFib: exp =
    let
      val a = Id.new "a"
      val b = Id.new "b"
      val aa = Id.new "aa"

      val loop = Id.new "loop"
      val loop' = Id.new "loop"
      val n = Id.new "n"

      val updStmt =
        Let (aa, Bang (Var a),
          Upd (Var b, OpAdd (Var aa, Upd (Var a, Bang (Var b)))))

      val loopFunc =
        Func (loop, n, IfZero (Var n, Bang (Var a),
          Seq (updStmt, App (Var loop, OpSub (Var n, Num 1)))))

      val impFib = Id.new "impFib"
      val x = Id.new "x"
    in
      Func (impFib, x,
        Let (a, Ref (Num 0),
        Let (b, Ref (Num 1),
        Let (loop', loopFunc,
        App (Var loop', Var x)))))
    end

end
