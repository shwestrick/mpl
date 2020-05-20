(* Assigns types to Lang terms based on an explicit timestamp ordering graph *)
structure CheckTimeStamps =
struct

  fun parens s = "(" ^ s ^ ")"

  structure Id = Identifier
  structure IdTable = TreeTable(Id)
  structure IdSet = TreeSet(Id)
  type var = Id.t

  structure StampGraph = AdjacencyGraph(Id)
  fun unions graphs = List.foldr StampGraph.union StampGraph.empty graphs
  type stamp = Id.t

  structure Typ =
  struct
    type s = stamp

    datatype t =
      Num of s
    | Ref of s * t * t
    | Array of s * t * t
    | Prod of s * t list
    | Func of s * (StampGraph.t * s * s) * t * t

    fun toString t =
      case t of
        Num s => "num@" ^ Id.toString s
      | Ref (s, t1, t2) =>
          parens (toString t1 ^ ", " ^ toString t2) ^ " ref@" ^ Id.toString s
      | Array (s, t1, t2) =>
          parens (toString t1 ^ ", " ^ toString t2) ^ " array@" ^ Id.toString s
      | Prod (s, ts) =>
          parens (String.concatWith " * " (List.map toString ts))
          ^ "@" ^ Id.toString s
      | Func (s, (ord, a1, a2), t1, t2) =>
          parens (toString t1 ^ " -> " ^ toString t2)
          ^ "[" ^ Id.toString a1 ^ "," ^ Id.toString a2 ^ ","
          ^ StampGraph.toString ord ^ "]"
          ^ "@" ^ Id.toString s

    fun equal x y =
      case (x, y) of
        (Num s, Num s') => Id.eq (s, s')
      | (Ref (s, t1, t2), Ref (s', t1', t2')) =>
          Id.eq (s, s') andalso equal t1 t1' andalso equal t2 t2'
      | (Array (s, t1, t2), Array (s', t1', t2')) =>
          Id.eq (s, s') andalso equal t1 t1' andalso equal t2 t2'
      | (Prod (s, ts), Prod (s', ts')) =>
          Id.eq (s, s')
          andalso List.length ts = List.length ts'
          andalso Util.allTrue (Util.zipWith equal ts ts')
      | (Func (s, (ord, a1, a2), t1, t2),
         Func (s', (ord', a1', a2'), t1', t2')) =>
          Id.eq (s, s') andalso
          StampGraph.equal (ord, ord') andalso
          Id.eq (a1, a1') andalso
          Id.eq (a2, a2') andalso
          equal t1 t1' andalso
          equal t2 t2'
      | _ => false

  end

  type typ = Typ.t

  datatype exp =
    Var    of typ * stamp * stamp * var
  | Num    of typ * stamp * stamp * int
  | Ref    of typ * stamp * stamp * exp
  | Upd    of typ * stamp * stamp * exp * exp
  | Bang   of typ * stamp * stamp * exp
  | Array  of typ * stamp * stamp * exp list
  | Alloc  of typ * stamp * stamp * exp
  | AUpd   of typ * stamp * stamp * exp * exp * exp
  | ASub   of typ * stamp * stamp * exp * exp
  | Length of typ * stamp * stamp * exp
  | Seq    of typ * stamp * stamp * exp * exp
  | App    of typ * stamp * stamp * exp * exp
  | Par    of typ * stamp * stamp * exp list
  | Tuple  of typ * stamp * stamp * exp list
  | Select of typ * stamp * stamp * int * exp
  | Let    of typ * stamp * stamp * var * exp * exp
  | Func   of typ * stamp * stamp * var * var * exp
  | IfZero of typ * stamp * stamp * exp * exp * exp
  | Op     of typ * stamp * stamp * string * (int * int -> int) * exp * exp

  fun typOf e =
    case e of
      Var (t, _, _, _) => t
    | Num (t, _, _, _) => t
    | Ref (t, _, _, _) => t
    | Bang (t, _, _, _) => t
    | Upd (t, _, _, _, _) => t
    | Array (t, _, _, _) => t
    | Alloc (t, _, _, _) => t
    | AUpd (t, _, _, _, _, _) => t
    | ASub (t, _, _, _, _) => t
    | Length (t, _, _, _) => t
    | Seq (t, _, _, _, _) => t
    | App (t, _, _, _, _) => t
    | Par (t, _, _, _) => t
    | Tuple (t, _, _, _) => t
    | Select (t, _, _, _, _) => t
    | Let (t, _, _, _, _, _) => t
    | Func (t, _, _, _, _, _) => t
    | IfZero (t, _, _, _, _, _) => t
    | Op (t, _, _, _, _, _, _) => t

  fun startOf e =
    case e of
      Var (_, d, _, _) => d
    | Num (_, d, _, _) => d
    | Ref (_, d, _, _) => d
    | Bang (_, d, _, _) => d
    | Upd (_, d, _, _, _) => d
    | Array (_, d, _, _) => d
    | Alloc (_, d, _, _) => d
    | AUpd (_, d, _, _, _, _) => d
    | ASub (_, d, _, _, _) => d
    | Length (_, d, _, _) => d
    | Seq (_, d, _, _, _) => d
    | App (_, d, _, _, _) => d
    | Par (_, d, _, _) => d
    | Tuple (_, d, _, _) => d
    | Select (_, d, _, _, _) => d
    | Let (_, d, _, _, _, _) => d
    | Func (_, d, _, _, _, _) => d
    | IfZero (_, d, _, _, _, _) => d
    | Op (_, d, _, _, _, _, _) => d

  fun endOf e =
    case e of
      Var (_, _, d, _) => d
    | Num (_, _, d, _) => d
    | Ref (_, _, d, _) => d
    | Bang (_, _, d, _) => d
    | Upd (_, _, d, _, _) => d
    | Array (_, _, d, _) => d
    | Alloc (_, _, d, _) => d
    | AUpd (_, _, d, _, _, _) => d
    | ASub (_, _, d, _, _) => d
    | Length (_, _, d, _) => d
    | Seq (_, _, d, _, _) => d
    | App (_, _, d, _, _) => d
    | Par (_, _, d, _) => d
    | Tuple (_, _, d, _) => d
    | Select (_, _, d, _, _) => d
    | Let (_, _, d, _, _, _) => d
    | Func (_, _, d, _, _, _) => d
    | IfZero (_, _, d, _, _, _) => d
    | Op (_, _, d, _, _, _, _) => d

  fun toString e =
    case e of
      Var (_, _, _, v) => Id.toString v
    | Num (_, _, _, n) => Int.toString n
    | Ref (_, _, _, e') => "ref " ^ toStringP e'
    | Bang (_, _, _, e') => "!" ^ toStringP e'
    | Upd (_, _, _, e1, e2) => toStringP e1 ^ " := " ^ toStringP e2
    | Array (_, _, _, es) => "[" ^ String.concatWith ", " (List.map toStringP es) ^ "]"
    | Alloc (_, _, _, e') => "alloc " ^ toStringP e'
    | AUpd (_, _, _, e1, e2, e3) =>
        toStringP e1 ^ "[" ^ toString e2 ^ "] := " ^ toString e3
    | ASub (_, _, _, e1, e2) =>
        toStringP e1 ^ "[" ^ toString e2 ^ "]"
    | Length (_, _, _, e') => "length " ^ toStringP e'
    | App (_, _, _, e1, e2) =>
        toStringP e1 ^ " " ^ toStringP e2
    | Seq (_, _, _, e1, e2) =>
        toStringP e1 ^ "; " ^ toStringP e2
    | Par (_, _, _, es) =>
        "(" ^ String.concatWith " || " (List.map toString es) ^ ")"
    | Tuple (_, _, _, es) =>
        "(" ^ String.concatWith ", " (List.map toString es) ^ ")"
    | Select (_, _, _, n, e') => "#" ^ Int.toString n ^ " " ^ toStringP e'
    | Let (_, _, _, v, e1, e2) =>
        let
          val vStr = Id.toString v ^ ": " ^ Typ.toString (typOf e1)
        in
          "let " ^ vStr ^ " = " ^ toString e1 ^ " in " ^ toString e2
        end
    | Func (t, _, _, func, arg, body) =>
        let
          val funcStr = "(" ^ Id.toString func ^ ": " ^ Typ.toString t ^ ")"
        in
          "fun " ^ funcStr ^ " " ^ Id.toString arg ^ " is " ^ toString body
        end
    | Op (_, _, _, name, _, e1, e2) =>
        toStringP e1 ^ " " ^ name ^ " " ^ toStringP e2
    | IfZero (_, _, _, e1, e2, e3) =>
        "ifz " ^ toString e1 ^ " then " ^ toString e2 ^ " else " ^ toString e3

  and toStringP e =
    let
      val needsP =
        case e of
          App _ => true
        | Op _ => true
        | IfZero _ => true
        | Select _ => true
        | Let _ => true
        | Func _ => true
        | Upd _ => true
        | Bang _ => true
        | Seq _ => true
        | Alloc _ => true
        | AUpd _ => true
        | ASub _ => true
        | Length _ => true
        | _ => false
    in
      if needsP then parens (toString e) else toString e
    end

  fun fold (p as {combine=c: 'a * 'b -> 'b,
                  typ: typ -> 'a,
                  var: var -> 'a,
                  num: int -> 'a})
           (b: 'b)
           (e: exp) =
    case e of
      Var (t, _, _, v) =>
        c (var v, c (typ t, b))
    | Num (t, _, _, n) =>
        c (num n, c (typ t, b))
    | Ref (t, _, _, e') =>
        fold p (c (typ t, b)) e'
    | Upd (t, _, _, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | Bang (t, _, _, e') =>
        fold p (c (typ t, b)) e'
    | Array (t, _, _, es) =>
        List.foldl (fn (ee, bb) => fold p bb ee) (c (typ t, b)) es
    | Alloc (t, _, _, e') =>
        fold p (c (typ t, b)) e'
    | Length (t, _, _, e') =>
        fold p (c (typ t, b)) e'
    | AUpd (t, _, _, e1, e2, e3) =>
        fold p (fold p (fold p (c (typ t, b)) e1) e2) e3
    | ASub (t, _, _, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | Seq (t, _, _, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | App (t, _, _, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | Par (t, _, _, es) =>
        List.foldl (fn (ee, bb) => fold p bb ee) (c (typ t, b)) es
    | Tuple (t, _, _, es) =>
        List.foldl (fn (ee, bb) => fold p bb ee) (c (typ t, b)) es
    | Select (t, _, _, _, e') =>
        fold p (c (typ t, b)) e'
    | Let (t, _, _, v, e1, e2) =>
        fold p (fold p (c (var v, c (typ t, b))) e1) e2
    | Func (t, _, _, f, x, e') =>
        fold p (c (var x, c (var f, c (typ t, b)))) e'
    | IfZero (t, _, _, e1, e2, e3) =>
        fold p (fold p (fold p (c (typ t, b)) e1) e2) e3
    | Op (t, _, _, _, _, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2

(*
  fun hasUnknowns e =
    fold {combine = (fn (a, b) => a orelse b),
          typ = Typ.hasUnknowns,
          var = (fn _ => false),
          num = (fn _ => false)}
         false
         e
*)

  fun equal e1 e2 =
    case (e1, e2) of
      (Var (t1, s1, s1', v1), Var (t2, s2, s2', v2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        Id.eq (v1, v2)
    | (Num (t1, s1, s1', n1), Num (t2, s2, s2', n2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        n1 = n2
    | (Ref (t1, s1, s1', x1), Ref (t2, s2, s2', x2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        equal x1 x2
    | (Bang (t1, s1, s1', x1), Bang (t2, s2, s2', x2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        equal x1 x2
    | (Upd (t1, s1, s1', x1, y1), Upd (t2, s2, s2', x2, y2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (Array (t1, s1, s1', es1), Array (t2, s2, s2', es2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        List.length es1 = List.length es2 andalso
        Util.allTrue (Util.zipWith equal es1 es2)
    | (Alloc (t1, s1, s1', x1), Alloc (t2, s2, s2', x2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        equal x1 x2
    | (Length (t1, s1, s1', x1), Length (t2, s2, s2', x2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        equal x1 x2
    | (ASub (t1, s1, s1', x1, y1), ASub (t2, s2, s2', x2, y2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (AUpd (t1, s1, s1', a1, b1, c1), AUpd (t2, s2, s2', a2, b2, c2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        equal a1 a2 andalso
        equal b1 b2 andalso
        equal c1 c2
    | (Seq (t1, s1, s1', x1, y1), Seq (t2, s2, s2', x2, y2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (App (t1, s1, s1', x1, y1), App (t2, s2, s2', x2, y2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (Par (t1, s1, s1', es1), Par (t2, s2, s2', es2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        List.length es1 = List.length es2 andalso
        Util.allTrue (Util.zipWith equal es1 es2)
    | (Tuple (t1, s1, s1', es1), Tuple (t2, s2, s2', es2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        List.length es1 = List.length es2 andalso
        Util.allTrue (Util.zipWith equal es1 es2)
    | (Select (t1, s1, s1', n1, x1), Select (t2, s2, s2', n2, x2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        n1 = n2 andalso
        equal x1 x2
    | (Let (t1, s1, s1', v1, a1, b1), Let (t2, s2, s2', v2, a2, b2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        Id.eq (v1, v2) andalso
        equal a1 a2 andalso
        equal b1 b2
    | (Func (t1, s1, s1', f1, a1, b1), Func (t2, s2, s2', f2, a2, b2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        Id.eq (f1, f2) andalso
        Id.eq (a1, a2) andalso
        equal b1 b2
    | (IfZero (t1, s1, s1', a1, b1, c1), IfZero (t2, s2, s2', a2, b2, c2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        equal a1 a2 andalso
        equal b1 b2 andalso
        equal c1 c2
    | (Op (t1, s1, s1', n1, _, a1, b1), Op (t2, s2, s2', n2, _, a2, b2)) =>
        Id.eq (s1, s2) andalso
        Id.eq (s1', s2') andalso
        Typ.equal t1 t2 andalso
        n1 = n2 andalso
        equal a1 a2 andalso
        equal b1 b2
    | _ => false

  (* ========================================================================
   * type checking, no inference
   *)

  exception NYI (* not yet implemented *)

  type check_typ_input =
    { ord: StampGraph.t
    , freshOrd: StampGraph.t
    , ctx: Typ.t IdTable.t
    }

  fun checkTypExp (stuff: check_typ_input) (e: exp): unit =
    case e of
      Var x    => checkTypVar stuff x
    | Num x    => checkTypNum stuff x
    | App x    => checkTypApp stuff x
    | Par x    => checkTypPar stuff x
    | Tuple x  => checkTypTuple stuff x
    | Select x => checkTypSelect stuff x
    | Let x    => checkTypLet stuff x
    | Op x     => checkTypOp stuff x
    | IfZero x => checkTypIfZero stuff x
    | Func x   => checkTypFunc stuff x
    | Ref x    => checkTypRef stuff x
    | Bang x   => checkTypBang stuff x
    | Upd x    => checkTypUpd stuff x
    | Seq x    => checkTypSeq stuff x
    | Array x  => checkTypArray stuff x
    | Alloc x  => checkTypAlloc stuff x
    | AUpd x   => checkTypAUpd stuff x
    | ASub x   => checkTypASub stuff x
    | Length x => checkTypLength stuff x

  and checkTypExpectVar stuff (e: exp) =
    case e of
      Var x => checkTypVar stuff x
    | _ => raise Fail ("CTS.checkTypExpectVar: expected var expression, but " ^
           "found " ^ toString e)

  and checkTypVar {ctx, ord, freshOrd} (t, startTime, endTime, v) =
    case IdTable.lookup v ctx of
      NONE => raise Fail ("CTS.checkTypVar: unknown var " ^ Id.toString v)
    | SOME t' =>
        if Typ.equal t t'
           andalso Id.eq (startTime, endTime)
           andalso StampGraph.isEmpty freshOrd
        then ()
        else raise Fail ("CTS.checkTypVar: type error")

  and checkTypNum {ctx, ord, freshOrd} (t, startTime, endTime, n) =
    if Typ.equal t (Typ.Num startTime)
       andalso Id.eq (startTime, endTime)
       andalso StampGraph.isEmpty freshOrd
    then ()
    else raise Fail ("CTS.checkTypNum: type error")

  and checkTypApp input x =
    raise NYI

  and checkTypPar {ctx, ord, freshOrd} (t, startTime, endTime, children) =
    let
      fun checkChild child =
        checkTypExp
          { ctx = ctx
          , ord = StampGraph.insertEdge (startTime, startOf child) ord
          , freshOrd =
              StampGraph.reachableFrom (startOf child)
              (StampGraph.removeVertex endTime freshOrd)
          }
          child
    in
      if Typ.equal t (Typ.Prod (endTime, List.map typOf children))
      then ()
      else raise Fail ("CTS.checkTypPar: type error");

      List.app checkChild children
    end

  and checkTypTuple stuff (t, startTime, endTime, children) =
    let
    in
      if Typ.equal t (Typ.Prod (endTime, List.map typOf children))
         andalso Id.eq (startTime, endTime)
         andalso StampGraph.isEmpty (#freshOrd stuff)
      then ()
      else raise Fail ("CTS.checkTypTuple: type error");

      List.app (checkTypExpectVar stuff) children
    end

  and checkTypSelect stuff (t, startTime, endTime, n, e) =
    let
      val expectedTyp =
        case typOf e of
          Typ.Prod (_, ts) =>
            (List.nth (ts, n-1)
             handle Subscript =>
               raise Fail ("CTS.checkTypSelect: index out-of-bounds"))
        | _ => raise Fail ("CTS.checkTypSelect: expected product")
    in
      if Typ.equal t expectedTyp
         andalso Id.eq (startTime, endTime)
         andalso StampGraph.isEmpty (#freshOrd stuff)
      then ()
      else raise Fail ("CTS.checkTypSelect: type error");

      checkTypExpectVar stuff e
    end

  and checkTypLet {ctx, ord, freshOrd} (t, startTime, endTime, v, e1, e2) =
    let
      val mid = startOf e2
      val pastMid =
        StampGraph.removeVertex mid (StampGraph.reachableFrom mid freshOrd)
      val T = StampGraph.transpose
      val upToMid = T (StampGraph.reachableFrom mid (T freshOrd))
    in
      if Id.eq (endOf e1, startOf e2)
      then ()
      else raise Fail ("CTS.checkTypLet: mid-point disagreement");

      if Typ.equal t (typOf e2)
      then ()
      else raise Fail ("CTS.checkTypLet: type error");

      checkTypExp
        { ctx = ctx
        , ord = ord
        , freshOrd = upToMid
        }
        e1;

      checkTypExp
        { ctx = IdTable.insert (v, typOf e1) ctx (* TODO: subtyping *)
        , ord = unions [ord, upToMid]
        , freshOrd = pastMid
        }
        e2
    end

  and checkTypOp stuff (t, startTime, endTime, _, _, e1, e2) =
    ( if Typ.equal t (Typ.Num startTime)
         andalso Id.eq (startTime, endTime)
         andalso StampGraph.isEmpty (#freshOrd stuff)
      then ()
      else raise Fail ("CTS.checkTypNum: type error")

    ; case typOf e1 of Typ.Num _ => () | _ =>
        raise Fail ("CTS.checkTypNum: type error on left operand")

    ; case typOf e2 of Typ.Num _ => () | _ =>
        raise Fail ("CTS.checkTypNum: type error on right operand")

    ; checkTypExpectVar stuff e1
    ; checkTypExpectVar stuff e2
    )

  and checkTypIfZero input x =
    raise NYI

  and checkTypFunc input (t, startTime, endTime, funcId, argId, body) =
    raise NYI

  and checkTypRef input x =
    raise NYI

  and checkTypBang input x =
    raise NYI

  and checkTypUpd input x =
    raise NYI

  and checkTypSeq input x =
    raise NYI

  and checkTypArray input x =
    raise NYI

  and checkTypAlloc input x =
    raise NYI

  and checkTypAUpd input x =
    raise NYI

  and checkTypASub input x =
    raise NYI

  and checkTypLength input x =
    raise NYI

  (* ====================================================================== *)

  (* fun OpAdd d (e1, e2) = Op (Typ.Num d, d, d, "+", op+, e1, e2)
  fun OpSub d (e1, e2) = Op (Typ.Num d, d, d, "-", op-, e1, e2)
  fun OpMul d (e1, e2) = Op (Typ.Num d, d, d, "*", op*, e1, e2)
  fun OpDiv d (e1, e2) = Op (Typ.Num d, d, d, "/", fn (x, y) => x div y, e1, e2)

  fun Fst t e = Select (1, e)
  fun Snd t e = Select (2, e)

  val parAdd: exp =
    let
      val left = OpAdd (Num 1, Num 2)
      val right = OpAdd (Num 3, Num 4)
      val x = Id.new "x"
    in
      Let (x, Par [left, right], OpAdd (Select (1, Var x), Select (2, Var x)))
    end *)

end
