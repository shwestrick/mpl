(* Lang0 has no types. Just raw AST *)
structure Lang0 =
struct

  structure Id = Identifier
  structure IdTable = TreeTable(Id)
  type var = Id.t
  (* type typ = Type.t *)

  type loc = Id.t

  val bogusLoc = Id.new "bogus"

  datatype exp =
    Var of var
  | Loc of loc (* "internal"; not visible to other langs *)

  | Ref of exp
  | Upd of exp * exp
  | Bang of exp

  | Array of exp list
  | Alloc of exp
  | AUpd of exp * exp * exp
  | ASub of exp * exp
  | Length of exp

  | Seq of exp * exp
  | App of exp * exp
  | Par of exp list   (* arbitrarily wide tuples *)
  | Tuple of exp list (* arbitrarily wide tuples *)
  | Select of int * exp
  | Let of var * exp * exp
  | Func of var * var * exp (* function name, argument, function body *)
  | Num of int
  | IfZero of exp * exp * exp
  | Op of string * (int * int -> int) * exp * exp

  fun OpAdd (e1, e2) = Op ("+", op+, e1, e2)
  fun OpSub (e1, e2) = Op ("-", op-, e1, e2)
  fun OpMul (e1, e2) = Op ("*", op*, e1, e2)
  fun OpDiv (e1, e2) = Op ("/", fn (x, y) => x div y, e1, e2)

  fun parens s = "(" ^ s ^ ")"

  fun toString e =
    case e of
      Var v => Id.toString v
    | Num n => Int.toString n
    | Loc l => Id.toString l
    | Ref e' => "ref " ^ toStringP e'
    | Bang e' => "!" ^ toStringP e'
    | Upd (e1, e2) => toStringP e1 ^ " := " ^ toStringP e2

    | Array es => "[" ^ String.concatWith ", " (List.map toStringP es) ^ "]"
    | Alloc e' => "alloc " ^ toStringP e'
    | AUpd (e1, e2, e3) =>
        toStringP e1 ^ "[" ^ toString e2 ^ "] := " ^ toString e3
    | ASub (e1, e2) =>
        toStringP e1 ^ "[" ^ toString e2 ^ "]"
    | Length e' => "length " ^ toStringP e'

    | App (e1, e2) =>
        toStringP e1 ^ " " ^ toStringP e2
    | Seq (e1, e2) =>
        toStringP e1 ^ " ; " ^ toStringP e2
    | Par es =>
        "(" ^ String.concatWith " || " (List.map toString es) ^ ")"
    | Tuple es =>
        "(" ^ String.concatWith ", " (List.map toString es) ^ ")"
    | Select (n, e') => "#" ^ Int.toString n ^ " " ^ toStringP e'
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
        | Op _ => true
        | Alloc _ => true
        | AUpd _ => true
        | ASub _ => true
        | Length _ => true
        | IfZero _ => true
        | Select _ => true
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
  fun deTuple e = case e of Tuple x => x | _ => raise Fail "deTuple"
  fun deRef e = case e of Ref x => x | _ => raise Fail "deRef"
  fun deArray e = case e of Array x => x | _ => raise Fail "deArray"

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

      | Array es => Array (List.map doit es)
      | Alloc e' => Alloc (doit e')
      | AUpd (e1, e2, e3) => AUpd (doit e1, doit e2, doit e3)
      | ASub (e1, e2) => ASub (doit e1, doit e2)
      | Length e' => Length (doit e')

      | App (e1, e2) => App (doit e1, doit e2)
      | Par es => Par (List.map doit es)
      | Seq (e1, e2) => Seq (doit e1, doit e2)
      | Tuple es => Tuple (List.map doit es)
      | Select (n, e') => Select (n, doit e')
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
      Var x    => NONE
    | Num x    => NONE
    | Loc x    => NONE
    | App x    => SOME (stepApp m x)
    | Par x    => SOME (stepPar m x)
    | Tuple x  => SOME (stepTuple m x)
    | Select x => SOME (stepSelect m x)
    | Let x    => SOME (stepLet m x)
    | Op x     => SOME (stepOp m x)
    | IfZero x => SOME (stepIfZero m x)
    | Func x   => SOME (stepFunc m x)
    | Ref x    => SOME (stepRef m x)
    | Bang x   => SOME (stepBang m x)
    | Upd x    => SOME (stepUpd m x)
    | Seq x    => SOME (stepSeq m x)
    | Array x  => SOME (stepArray m x)
    | Alloc x  => SOME (stepAlloc m x)
    | AUpd x   => SOME (stepAUpd m x)
    | ASub x   => SOME (stepASub m x)
    | Length x => SOME (stepLength m x)

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

  and stepPar m es =
    case stepFirstThatCan m es of
      SOME (m', es') => (m', Par es')
    | NONE => (m, Tuple es)

  and stepTuple m es =
    case stepFirstThatCan m es of
      SOME (m', es') => (m', Tuple es')
    | NONE =>
        let
          val l = Id.loc ()
        in
          (IdTable.insert (l, Tuple es) m, Loc l)
        end

  and stepArray m es =
    case stepFirstThatCan m es of
      SOME (m', es') => (m', Array es')
    | NONE =>
        let
          val l = Id.loc ()
        in
          (IdTable.insert (l, Array es) m, Loc l)
        end

  and stepAlloc m e =
    case step (m, e) of
      SOME (m', e') => (m', Alloc e')
    | NONE =>
        let
          val n = deNum e

          (* cheat by initializing with a bunch of bogus pointers *)
          val es = List.tabulate (n, fn _ => Loc bogusLoc)
          val l = Id.loc ()
        in
          (IdTable.insert (l, Array es) m, Loc l)
        end

  and stepAUpd m (e1, e2, e3) =
    case step (m, e1) of
      SOME (m', e1') => (m', AUpd (e1', e2, e3))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', AUpd (e1, e2', e3))
        | NONE =>
            case step (m, e3) of
                SOME (m', e3') => (m', AUpd (e1, e2, e3'))
              | NONE =>
                  let
                    val l = deLoc e1
                    val es = deArray (getLoc l m)
                    val idx = deNum e2

                    (* jump to idx and replace with e3 *)
                    val es' =
                      List.take (es, idx) @ (e3 :: List.drop (es, idx+1))
                  in
                    (IdTable.insert (l, Array es') m, e3)
                  end

  and stepASub m (e1, e2) =
    case step (m, e1) of
      SOME (m', e1') => (m', ASub (e1', e2))
    | NONE =>
        case step (m, e2) of
          SOME (m', e2') => (m', ASub (e1, e2'))
        | NONE =>
            let
              val l = deLoc e1
              val es = deArray (getLoc l m)
              val idx = deNum e2
            in
              (m, List.nth (es, idx))
            end

  and stepLength m e =
    case step (m, e) of
      SOME (m', e') => (m', Length e')
    | NONE =>
        let
          val es = deArray (getLoc (deLoc e) m)
        in
          (m, Num (List.length es))
        end

  (* Walk through es, trying to step each expression, from left to right.
   * as soon as we find an e -> e', we replace e with e' and back out,
   * returning the updated memory. If no expression can step, then we
   * are done stepping this group of expressions. This is used to implement
   * both Tuple stepping, and Par stepping. Really, Par stepping should be
   * parallel or interleaved, but whatever.
   *)
  and stepFirstThatCan m es =
    case es of
      [] => NONE
    | e :: rest =>
        case step (m, e) of
          SOME (m', e') => SOME (m', e' :: rest)
        | NONE =>
            case stepFirstThatCan m rest of
              SOME (m', rest') => SOME (m', e :: rest')
            | NONE => NONE

  and stepSelect m (n, e) =
    case step (m, e) of
      SOME (m', e') => (m', Select (n, e'))
    | NONE =>
        (m, List.nth (deTuple (getLoc (deLoc e) m), n-1))

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

  fun Fst e = Select (1, e)
  fun Snd e = Select (2, e)

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
      Let (ff, idFunc, Par [App (Var ff, Num 1), App (Var ff, (Par [Num 2, Num 3]))])
    end

  val parAdd: exp =
    let
      val left = OpAdd (Num 1, Num 2)
      val right = OpAdd (Num 3, Num 4)
      val x = Id.new "x"
    in
      Let (x, Par [left, right], OpAdd (Select (1, Var x), Select (2, Var x)))
    end

  val iterFib: exp =
    let
      (* iterFib takes x = (a, b, n) where a and b are the two most recent *)
      val iterFib = Id.new "iterFib"
      val x = Id.new "x"
      val a = Select (1, Var x)
      val b = Select (2, Var x)
      val n = Select (3, Var x)
      val elseBranch =
        App (Var iterFib, Tuple [b, OpAdd (a, b), OpSub (n, Num 1)])
      val body = IfZero (n, a, elseBranch)
    in
      Func (iterFib, x, body)
    end

  val fib: exp =
    let
      val fib = Id.new "fib"
      val n = Id.new "n"
    in
      Func (fib, n, App (iterFib, Tuple [Num 0, Num 1, Var n]))
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

  val sum: exp =
    let
      val sum = Id.new "sum"
      val range = Id.new "range"
      val i = Id.new "i"
      val j = Id.new "j"
      val mid = Id.new "mid"
      val c = Id.new "c"

      val body =
        Let (i, Select (1, Var range),
        Let (j, Select (2, Var range),
          IfZero (OpSub (Var j, Var i), Num 0,
          IfZero (OpSub (Var j, OpAdd (Var i, Num 1)), Var i,
          Let (mid, OpAdd (Var i, OpDiv (OpSub (Var j, Var i), Num 2)),
          Let (c, Par [App (Var sum, Tuple [Var i, Var mid]),
                       App (Var sum, Tuple [Var mid, Var j])],
            OpAdd (Select (1, Var c), Select (2, Var c))))))))
    in
      Func (sum, range, body)
    end

  val sumArray: exp =
    let
      val sumRange = Id.new "sumRange"
      val range = Id.new "range"
      val i = Id.new "i"
      val j = Id.new "j"
      val a = Id.new "a"
      val mid = Id.new "mid"
      val c = Id.new "c"

      val body =
        Let (i, Select (1, Var range),
        Let (j, Select (2, Var range),
          IfZero (OpSub (Var j, Var i), Num 0,
          IfZero (OpSub (Var j, OpAdd (Var i, Num 1)), ASub (Var a, Var i),
          Let (mid, OpAdd (Var i, OpDiv (OpSub (Var j, Var i), Num 2)),
          Let (c, Par [App (Var sumRange, Tuple [Var i, Var mid]),
                       App (Var sumRange, Tuple [Var mid, Var j])],
            OpAdd (Select (1, Var c), Select (2, Var c))))))))

      val sumArray = Id.new "sumArray"
    in
      Func (sumArray, a,
        App (Func (sumRange, range, body),
             Tuple [Num 0, Length (Var a)]))
    end

end
