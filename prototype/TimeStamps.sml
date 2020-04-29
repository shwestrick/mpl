(* Assigns types to Lang terms based on an explicit timestamp ordering graph *)
structure TimeStamps =
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

(*
    exception Overconstrained

    fun glb x y =
      case (x, y) of
        (Unknown, _) => y
      | (_, Unknown) => x
      | (Num d, Num d') => Num (min d d')
      | (Ref (d, t1, t2), Ref (d', t1', t2')) =>
          Ref (min d d', lub t1 t1', glb t2 t2')
      | (Array (d, t1, t2), Array (d', t1', t2')) =>
          Array (min d d', lub t1 t1', glb t2 t2')
      | (Func (d, t1, t2), Func (d', t1', t2')) =>
          Func (min d d', lub t1 t1', glb t2 t2')
      | (Prod (d, ts), Prod (d', ts')) =>
          if List.length ts = List.length ts' then
            Prod (min d d', Util.zipWith glb ts ts')
          else
            raise Overconstrained
      | _ => raise Overconstrained

    and lub x y =
      case (x, y) of
        (Unknown, _) => y
      | (_, Unknown) => x
      | (Num d, Num d') => Num (max d d')
      | (Ref (d, t1, t2), Ref (d', t1', t2')) =>
          Ref (max d d', glb t1 t1', lub t2 t2')
      | (Array (d, t1, t2), Array (d', t1', t2')) =>
          Array (max d d', glb t1 t1', lub t2 t2')
      | (Func (d, t1, t2), Func (d', t1', t2')) =>
          Func (max d d', glb t1 t1', lub t2 t2')
      | (Prod (d, ts), Prod (d', ts')) =>
          if List.length ts = List.length ts' then
            Prod (max d d', Util.zipWith lub ts ts')
          else
            raise Overconstrained
      | _ => raise Overconstrained

    fun unify (t1, t2) = glb t1 t2
*)

  end

  type typ = Typ.t

  datatype exp =
    Var of typ * var
  | Num of typ * int
  | Ref of typ * exp
  | Upd of typ * exp * exp
  | Bang of typ * exp
  | Array of typ * exp list
  | Alloc of typ * exp
  | AUpd of typ * exp * exp * exp
  | ASub of typ * exp * exp
  | Length of typ * exp
  | Seq of typ * exp * exp
  | App of typ * exp * exp
  | Par of typ * exp list
  | Tuple of typ * exp list
  | Select of typ * int * exp
  | Let of typ * var * exp * exp
  | Func of typ * var * var * exp
  | IfZero of typ * exp * exp * exp
  | Op of typ * string * (int * int -> int) * exp * exp

  fun typOf e =
    case e of
      Var (t, _) => t
    | Num (t, _) => t
    | Ref (t, _) => t
    | Bang (t, _) => t
    | Upd (t, _, _) => t
    | Array (t, _) => t
    | Alloc (t, _) => t
    | AUpd (t, _, _, _) => t
    | ASub (t, _, _) => t
    | Length (t, _) => t
    | Seq (t, _, _) => t
    | App (t, _, _) => t
    | Par (t, _) => t
    | Tuple (t, _) => t
    | Select (t, _, _) => t
    | Let (t, _, _, _) => t
    | Func (t, _, _, _) => t
    | IfZero (t, _, _, _) => t
    | Op (t, _, _, _, _) => t

  fun toString e =
    case e of
      Var (_, v) => Id.toString v
    | Num (_, n) => Int.toString n
    | Ref (_, e') => "ref " ^ toStringP e'
    | Bang (_, e') => "!" ^ toStringP e'
    | Upd (_, e1, e2) => toStringP e1 ^ " := " ^ toStringP e2
    | Array (_, es) => "[" ^ String.concatWith ", " (List.map toStringP es) ^ "]"
    | Alloc (_, e') => "alloc " ^ toStringP e'
    | AUpd (_, e1, e2, e3) =>
        toStringP e1 ^ "[" ^ toString e2 ^ "] := " ^ toString e3
    | ASub (_, e1, e2) =>
        toStringP e1 ^ "[" ^ toString e2 ^ "]"
    | Length (_, e') => "length " ^ toStringP e'
    | App (_, e1, e2) =>
        toStringP e1 ^ " " ^ toStringP e2
    | Seq (_, e1, e2) =>
        toStringP e1 ^ "; " ^ toStringP e2
    | Par (_, es) =>
        "(" ^ String.concatWith " || " (List.map toString es) ^ ")"
    | Tuple (_, es) =>
        "(" ^ String.concatWith ", " (List.map toString es) ^ ")"
    | Select (_, n, e') => "#" ^ Int.toString n ^ " " ^ toStringP e'
    | Let (_, v, e1, e2) =>
        let
          val vStr = Id.toString v ^ ": " ^ Typ.toString (typOf e1)
        in
          "let " ^ vStr ^ " = " ^ toString e1 ^ " in " ^ toString e2
        end
    | Func (t, func, arg, body) =>
        let
          val funcStr = "(" ^ Id.toString func ^ ": " ^ Typ.toString t ^ ")"
        in
          "fun " ^ funcStr ^ " " ^ Id.toString arg ^ " is " ^ toString body
        end
    | Op (_, name, _, e1, e2) =>
        toStringP e1 ^ " " ^ name ^ " " ^ toStringP e2
    | IfZero (_, e1, e2, e3) =>
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
      Var (t, v) =>
        c (var v, c (typ t, b))
    | Num (t, n) =>
        c (num n, c (typ t, b))
    | Ref (t, e') =>
        fold p (c (typ t, b)) e'
    | Upd (t, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | Bang (t, e') =>
        fold p (c (typ t, b)) e'
    | Array (t, es) =>
        List.foldl (fn (ee, bb) => fold p bb ee) (c (typ t, b)) es
    | Alloc (t, e') =>
        fold p (c (typ t, b)) e'
    | Length (t, e') =>
        fold p (c (typ t, b)) e'
    | AUpd (t, e1, e2, e3) =>
        fold p (fold p (fold p (c (typ t, b)) e1) e2) e3
    | ASub (t, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | Seq (t, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | App (t, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | Par (t, es) =>
        List.foldl (fn (ee, bb) => fold p bb ee) (c (typ t, b)) es
    | Tuple (t, es) =>
        List.foldl (fn (ee, bb) => fold p bb ee) (c (typ t, b)) es
    | Select (t, _, e') =>
        fold p (c (typ t, b)) e'
    | Let (t, v, e1, e2) =>
        fold p (fold p (c (var v, c (typ t, b))) e1) e2
    | Func (t, f, x, e') =>
        fold p (c (var x, c (var f, c (typ t, b)))) e'
    | IfZero (t, e1, e2, e3) =>
        fold p (fold p (fold p (c (typ t, b)) e1) e2) e3
    | Op (t, _, _, e1, e2) =>
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
      (Var (t1, v1), Var (t2, v2)) =>
        Typ.equal t1 t2 andalso
        Id.eq (v1, v2)
    | (Num (t1, n1), Num (t2, n2)) =>
        Typ.equal t1 t2 andalso
        n1 = n2
    | (Ref (t1, x1), Ref (t2, x2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2
    | (Bang (t1, x1), Bang (t2, x2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2
    | (Upd (t1, x1, y1), Upd (t2, x2, y2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (Array (t1, es1), Array (t2, es2)) =>
        Typ.equal t1 t2 andalso
        List.length es1 = List.length es2 andalso
        Util.allTrue (Util.zipWith equal es1 es2)
    | (Alloc (t1, x1), Alloc (t2, x2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2
    | (Length (t1, x1), Length (t2, x2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2
    | (ASub (t1, x1, y1), ASub (t2, x2, y2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (AUpd (t1, a1, b1, c1), AUpd (t2, a2, b2, c2)) =>
        Typ.equal t1 t2 andalso
        equal a1 a2 andalso
        equal b1 b2 andalso
        equal c1 c2
    | (Seq (t1, x1, y1), Seq (t2, x2, y2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (App (t1, x1, y1), App (t2, x2, y2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (Par (t1, es1), Par (t2, es2)) =>
        Typ.equal t1 t2 andalso
        List.length es1 = List.length es2 andalso
        Util.allTrue (Util.zipWith equal es1 es2)
    | (Tuple (t1, es1), Tuple (t2, es2)) =>
        Typ.equal t1 t2 andalso
        List.length es1 = List.length es2 andalso
        Util.allTrue (Util.zipWith equal es1 es2)
    | (Select (t1, n1, x1), Select (t2, n2, x2)) =>
        Typ.equal t1 t2 andalso
        n1 = n2 andalso
        equal x1 x2
    | (Let (t1, v1, a1, b1), Let (t2, v2, a2, b2)) =>
        Typ.equal t1 t2 andalso
        Id.eq (v1, v2) andalso
        equal a1 a2 andalso
        equal b1 b2
    | (Func (t1, f1, a1, b1), Func (t2, f2, a2, b2)) =>
        Typ.equal t1 t2 andalso
        Id.eq (f1, f2) andalso
        Id.eq (a1, a2) andalso
        equal b1 b2
    | (IfZero (t1, a1, b1, c1), IfZero (t2, a2, b2, c2)) =>
        Typ.equal t1 t2 andalso
        equal a1 a2 andalso
        equal b1 b2 andalso
        equal c1 c2
    | (Op (t1, n1, _, a1, b1), Op (t2, n2, _, a2, b2)) =>
        Typ.equal t1 t2 andalso
        n1 = n2 andalso
        equal a1 a2 andalso
        equal b1 b2
    | _ => false

  (* =========================================================================
   * type inference
   *)

  exception NYI (* not yet implemented *)

  type stamp_exp_input =
    { exp: ShapeTyping.exp
    , ord: StampGraph.t
    , ctx: Typ.t IdTable.t
    , startTime: stamp
    }

  type stamp_exp_output =
    { exp: exp
    , fresh: StampGraph.t
    , endTime: stamp
    }

  fun stampExp (stuff: stamp_exp_input) : stamp_exp_output =
    case #exp stuff of
      ShapeTyping.Var x    => stampVar stuff x
    | ShapeTyping.Num x    => stampNum stuff x
    | ShapeTyping.App x    => stampApp stuff x
    | ShapeTyping.Par x    => stampPar stuff x
    | ShapeTyping.Tuple x  => stampTuple stuff x
    | ShapeTyping.Select x => stampSelect stuff x
    | ShapeTyping.Let x    => stampLet stuff x
    | ShapeTyping.Op x     => stampOp stuff x
    | ShapeTyping.IfZero x => stampIfZero stuff x
    | ShapeTyping.Func x   => stampFunc stuff x
    | ShapeTyping.Ref x    => stampRef stuff x
    | ShapeTyping.Bang x   => stampBang stuff x
    | ShapeTyping.Upd x    => stampUpd stuff x
    | ShapeTyping.Seq x    => stampSeq stuff x
    | ShapeTyping.Array x  => stampArray stuff x
    | ShapeTyping.Alloc x  => stampAlloc stuff x
    | ShapeTyping.AUpd x   => stampAUpd stuff x
    | ShapeTyping.ASub x   => stampASub stuff x
    | ShapeTyping.Length x => stampLength stuff x

  and stampVar {ord, ctx, startTime, ...} (_, v) =
    case IdTable.lookup v ctx of
      NONE => raise Fail ("TS.stampVar: unknown var " ^ Id.toString v)
    | SOME t =>
        { exp = Var (t, v)
        , fresh = StampGraph.empty
        , endTime = startTime
        }

  and stampNum {ord, ctx, startTime, ...} (_, n) =
    { exp = Num (Typ.Num startTime, n)
    , fresh = StampGraph.empty
    , endTime = startTime
    }

  and stampApp {ord, ctx, startTime, ...} x =
    raise NYI

  and stampPar {ord, ctx, startTime, ...} (_, es) =
    let
      fun stampChild child =
        let
          val childStartTime = Id.stamp ()
          val {exp=child', fresh, endTime=childEndTime} =
            stampExp
            { ord = StampGraph.insertEdge (startTime, childStartTime) ord
            , ctx = ctx
            , startTime = childStartTime
            , exp = child
            }
        in
          (childStartTime, childEndTime, fresh, child')
        end

      val results = List.map stampChild es

      val endTime = Id.stamp ()

      val forkEdges =
        StampGraph.fromEdges
        (List.map (fn (childStart, _, _, _) => (startTime, childStart)) results)

      val joinEdges =
        StampGraph.fromEdges
        (List.map (fn (_, childEnd, _, _) => (childEnd, endTime)) results)

      val childFresh = unions (List.map (fn (_, _, ff, _) => ff) results)

      val children = List.map (fn (_, _, _, e) => e) results

      val typ = Typ.Prod (endTime, List.map typOf children)
    in
      { exp = Par (typ, children)
      , endTime = endTime
      , fresh = unions [forkEdges, childFresh, joinEdges]
      }
    end

  and stampTuple {ord, ctx, startTime, ...} x =
    raise NYI

  and stampSelect {ord, ctx, startTime, ...} x =
    raise NYI

  and stampLet {ord, ctx, startTime, ...} x =
    raise NYI

  and stampOp {ord, ctx, startTime, ...} x =
    raise NYI

  and stampIfZero {ord, ctx, startTime, ...} x =
    raise NYI

  and stampFunc {ord, ctx, startTime, ...} x =
    raise NYI

  and stampRef {ord, ctx, startTime, ...} x =
    raise NYI

  and stampBang {ord, ctx, startTime, ...} x =
    raise NYI

  and stampUpd {ord, ctx, startTime, ...} x =
    raise NYI

  and stampSeq {ord, ctx, startTime, ...} x =
    raise NYI

  and stampArray {ord, ctx, startTime, ...} x =
    raise NYI

  and stampAlloc {ord, ctx, startTime, ...} x =
    raise NYI

  and stampAUpd {ord, ctx, startTime, ...} x =
    raise NYI

  and stampASub {ord, ctx, startTime, ...} x =
    raise NYI

  and stampLength {ord, ctx, startTime, ...} x =
    raise NYI


  (* fun inferType (exp: Lang.exp): exp =
    let
      val shaped = ShapeTyping.inferType exp
    in
    end *)

end
