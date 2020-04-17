(* Assigns basic ML types to Lang terms. Very simple unification algorithm.
 * No polymorphism *)
structure ShapeTyping =
struct

  fun parens s = "(" ^ s ^ ")"

  structure Id = Identifier
  structure IdTable = TreeTable(Id)
  structure IdSet = TreeSet(Id)
  type var = Id.t

  structure Typ =
  struct

    datatype t =
      Unknown
    | Num
    | Ref of t
    | Array of t
    | Prod of t list
    | Func of t * t

    fun toString t =
      case t of
        Unknown => "_"
      | Num => "num"
      | Ref (t1) =>
          parens (toString t1) ^ " ref"
      | Array (t1) =>
          parens (toString t1) ^ " array"
      | Prod ts =>
          parens (String.concatWith " * " (List.map toString ts))
      | Func (t1, t2) =>
          parens (toString t1 ^ " -> " ^ toString t2)

    fun equal x y =
      case (x, y) of
        (Unknown, Unknown) => true
      | (Num, Num) => true
      | (Ref (t1), Ref (t1')) =>
          equal t1 t1'
      | (Array (t1), Array (t1')) =>
          equal t1 t1'
      | (Prod ts, Prod ts') =>
          List.length ts = List.length ts'
          andalso Util.allTrue (Util.zipWith equal ts ts')
      | (Func (t1, t2), Func (t1', t2')) =>
          equal t1 t1' andalso equal t2 t2'
      | _ => false

    fun hasUnknowns ty =
      case ty of
        Unknown => true
      | Ref (t1) => hasUnknowns t1
      | Array (t1) => hasUnknowns t1
      | Prod ts => List.exists hasUnknowns ts
      | Func (t1, t2) => hasUnknowns t1 orelse hasUnknowns t2
      | _ => false

    exception Overconstrained

    fun unify (t1, t2) =
      case (t1, t2) of
        (Unknown, _) => t2
      | (_, Unknown) => t1
      | (Num, Num) => Num
      | (Ref x, Ref y) => Ref (unify (x, y))
      | (Array x, Array y) => Array (unify (x, y))
      | (Prod xs, Prod ys) =>
          if List.length xs = List.length ys
          then Prod (Util.zipWith (fn a => fn b => unify (a, b)) xs ys)
          else raise Overconstrained
      | (Func (a, b), Func (c, d)) =>
          Func (unify (a, c), unify (b, d))
      | _ => raise Overconstrained

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

  val uu = Typ.Unknown

  fun fromLang (exp: Lang.exp): exp =
    case exp of
      Lang.Loc _ => raise Fail ("ST does not have locations")
    | Lang.Num n => Num (uu, n)
    | Lang.Var v => Var (uu, v)
    | Lang.Ref e => Ref (uu, fromLang e)
    | Lang.Bang e => Bang (uu, fromLang e)
    | Lang.Upd (e1, e2) => Upd (uu, fromLang e1, fromLang e2)
    | Lang.Seq (e1, e2) => Seq (uu, fromLang e1, fromLang e2)
    | Lang.App (e1, e2) => App (uu, fromLang e1, fromLang e2)
    | Lang.Array es => Array (uu, List.map fromLang es)
    | Lang.Alloc e => Alloc (uu, fromLang e)
    | Lang.AUpd (e1, e2, e3) =>
        AUpd (uu, fromLang e1, fromLang e2, fromLang e3)
    | Lang.ASub (e1, e2) => ASub (uu, fromLang e1, fromLang e2)
    | Lang.Length e => Length (uu, fromLang e)
    | Lang.Par es => Par (uu, List.map fromLang es)
    | Lang.Tuple es => Tuple (uu, List.map fromLang es)
    | Lang.Select (n, e') => Select (uu, n, fromLang e')
    | Lang.Let (v, e1, e2) => Let (uu, v, fromLang e1, fromLang e2)
    | Lang.Func (f, a, b) => Func (uu, f, a, fromLang b)
    | Lang.Op (name, f, e1, e2) => Op (uu, name, f, fromLang e1, fromLang e2)
    | Lang.IfZero (e1, e2, e3) =>
        IfZero (uu, fromLang e1, fromLang e2, fromLang e3)

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

  fun hasUnknowns e =
    fold {combine = (fn (a, b) => a orelse b),
          typ = Typ.hasUnknowns,
          var = (fn _ => false),
          num = (fn _ => false)}
         false
         e

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
   * scope checking
   *)

  fun checkScoping (vars: IdSet.t) (ctx: IdSet.t) (exp: exp) : IdSet.t =
    case exp of
      Num _ => vars
    | Var (_, v) =>
        if not (IdSet.member v ctx) then
          raise Fail ("ST.checkScoping Var: "
                      ^ Id.toString v ^ " not in scope")
        else
          vars
    | Ref (_, e) =>
        checkScoping vars ctx e
    | Bang (_, e) =>
        checkScoping vars ctx e
    | Upd (_, e1, e2) =>
        checkScoping (checkScoping vars ctx e1) ctx e2
    | Alloc (_, e) =>
        checkScoping vars ctx e
    | Array (_, es) =>
        List.foldl (fn (e, vars) => checkScoping vars ctx e) vars es
    | Length (_, e) =>
        checkScoping vars ctx e
    | ASub (_, e1, e2) =>
        checkScoping (checkScoping vars ctx e1) ctx e2
    | AUpd (_, e1, e2, e3) =>
        checkScoping (checkScoping (checkScoping vars ctx e1) ctx e2) ctx e3
    | Seq (_, e1, e2) =>
        checkScoping (checkScoping vars ctx e1) ctx e2
    | App (_, e1, e2) =>
        checkScoping (checkScoping vars ctx e1) ctx e2
    | Par (_, es) =>
        List.foldl (fn (e, vars) => checkScoping vars ctx e) vars es
    | Tuple (_, es) =>
        List.foldl (fn (e, vars) => checkScoping vars ctx e) vars es
    | Select (_, _, e) =>
        checkScoping vars ctx e
    | Let (_, v, e1, e2) =>
        if IdSet.member v vars then
          raise Fail ("ST.checkScoping Let: "
                      ^ Id.toString v ^ " not uniquely bound")
        else
          let
            val vars = IdSet.insert v vars
            val vars = checkScoping vars ctx e1
            val ctx' = IdSet.insert v ctx
          in
            checkScoping vars ctx' e2
          end
    | Func (_, func, arg, body) =>
        if IdSet.member func vars then
          raise Fail ("ST.checkScoping Func: "
                      ^ Id.toString func ^ " not uniquely bound")
        else if IdSet.member arg vars then
          raise Fail ("ST.checkScoping Func: "
                      ^ Id.toString arg ^ " not uniquely bound")
        else
          let
            val vars = IdSet.insert func vars
            val vars = IdSet.insert arg vars
            val ctx' = IdSet.insert arg (IdSet.insert func ctx)
          in
            checkScoping vars ctx' body
          end
    | Op (_, _, _, e1, e2) =>
        checkScoping (checkScoping vars ctx e1) ctx e2
    | IfZero (_, e1, e2, e3) =>
        checkScoping (checkScoping (checkScoping vars ctx e1) ctx e2) ctx e3

  (* =========================================================================
   * Type refinement
   *)

  fun refineRootTyp exp t' =
    let
      fun doit t = Typ.unify (t, t')
    in
      case exp of
        Var (t, v) => Var (doit t, v)
      | Num (t, n) => Num (doit t, n)
      | Ref (t, e) => Ref (doit t, e)
      | Bang (t, e) => Bang (doit t, e)
      | Upd (t, e1, e2) => Upd (doit t, e1, e2)

      | Array (t, es) => Array (doit t, es)
      | Alloc (t, e) => Alloc (doit t, e)
      | Length (t, e) => Length (doit t, e)
      | ASub (t, e1, e2) => ASub (doit t, e1, e2)
      | AUpd (t, e1, e2, e3) => AUpd (doit t, e1, e2, e3)

      | Seq (t, e1, e2) => Seq (doit t, e1, e2)
      | App (t, e1, e2) => App (doit t, e1, e2)
      | Par (t, es) => Par (doit t, es)
      | Tuple (t, es) => Tuple (doit t, es)
      | Select (t, n, e') => Select (doit t, n, e')
      | Let (t, v, e1, e2) => Let (doit t, v, e1, e2)
      | Func (t, func, arg, body) => Func (doit t, func, arg, body)
      | Op (t, name, f, e1, e2) => Op (doit t, name, f, e1, e2)
      | IfZero (t, e1, e2, e3) => IfZero (doit t, e1, e2, e3)
    end

  exception Overconstrained = Typ.Overconstrained

  fun refineTyp {vars: Typ.t IdTable.t, exp: exp}
               : {vars: Typ.t IdTable.t, exp: exp} =
    case exp of
      Var (t, v) =>
        (case IdTable.lookup v vars of
          NONE =>
            {vars = IdTable.insert (v, t) vars,
             exp = Var (t, v)}
        | SOME t' =>
            let
              val t'' = Typ.unify (t, t')
                handle Overconstrained =>
                raise Fail ("ST.refineTyp Var: "
                ^ "expected type " ^ Typ.toString t ^ " but found variable "
                ^ Id.toString v ^ " of type " ^ Typ.toString t')
            in
              (* if Typ.equal t' t'' then () else
                print ("var " ^ Id.toString v ^ " needs to have type "
                       ^ Typ.toString t
                       ^ " and was previously recorded as having type "
                       ^ Typ.toString t'
                       ^ "; now updating it to "
                       ^ Typ.toString t''
                       ^ "\n"); *)

              {vars = IdTable.insert (v, t'') vars,
               exp = Var (t'', v)}
            end)

    | Num (t, n) =>
        ({vars = vars, exp = Num (Typ.unify (t, Typ.Num), n)}
            handle Overconstrained =>
            raise Fail ("ST.refineTyp Num: expected type "
            ^ Typ.toString t ^ " but found type "
            ^ Typ.toString (Typ.Num)))

    | App (t, e1, e2) =>
        let
          val t1 = Typ.Func (typOf e2, t)
          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp App: expected function of type "
                  ^ Typ.toString t1 ^ " but found " ^ Typ.toString (typOf e1))
              }

          val (t2, t') =
            case typOf e1' of
              Typ.Func (t2, t') => (t2, t')
            | _ => raise Fail ("ST.refineTyp App: bug in refinement of e1")

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t2
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp App: function expects argument "
                  ^ "of type " ^ Typ.toString t2 ^ " but found type "
                  ^ Typ.toString (typOf e2))
              }
        in
          { vars = vars
          , exp = App (Typ.unify (t, t'), e1', e2')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp App: bug in final refinement")
          }
        end

    | Par (t, es) =>
        let
          fun refineSubExps vars idx ets =
            case ets of
              [] => (vars, [])
            | ((ee, tee) :: rest) =>
                let
                  val {vars, exp=ee'} =
                    refineTyp
                      { vars = vars
                      , exp = refineRootTyp ee tee
                          handle Overconstrained =>
                          raise Fail ("ST.refineTyp Par: "
                          ^ "expected component #" ^ Int.toString idx
                          ^ "of type " ^ Typ.toString tee ^ " but found "
                          ^ Typ.toString (typOf ee))
                      }

                  val (vars, rest') = refineSubExps vars (idx+1) rest
                in
                  (vars, ee' :: rest')
                end

          val n = List.length es
          val default = List.tabulate (n, fn _ => Typ.Unknown)
          val ts =
            case t of
              Typ.Prod (x) => if List.length x = n then x else default
            | _ => default

          val ets =
            Util.zipWith (fn ee => fn tee => (ee, tee)) es ts

          val (vars, es') = refineSubExps vars 1 ets

          val t' = Typ.Prod (List.map typOf es')
        in
          { vars = vars
          , exp = Par (Typ.unify (t, t'), es')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Par: bug in final refinement")
          }
        end

    | Tuple (t, es) =>
        let
          fun refineSubExps vars idx ets =
            case ets of
              [] => (vars, [])
            | ((ee, tee) :: rest) =>
                let
                  val {vars, exp=ee'} =
                    refineTyp
                      { vars = vars
                      , exp = refineRootTyp ee tee
                          handle Overconstrained =>
                          raise Fail ("ST.refineTyp Tuple: "
                          ^ "expected component #" ^ Int.toString idx
                          ^ "of type " ^ Typ.toString tee ^ " but found "
                          ^ Typ.toString (typOf ee))
                      }

                  val (vars, rest') = refineSubExps vars (idx+1) rest
                in
                  (vars, ee' :: rest')
                end

          val n = List.length es
          val default = List.tabulate (n, fn _ => Typ.Unknown)
          val ts =
            case t of
              Typ.Prod (x) => if List.length x = n then x else default
            | _ => default

          val ets =
            Util.zipWith (fn ee => fn tee => (ee, tee)) es ts

          val (vars, es') = refineSubExps vars 1 ets

          val t' = Typ.Prod (List.map typOf es')
        in
          { vars = vars
          , exp = Tuple (Typ.unify (t, t'), es')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Tuple: bug in final refinement")
          }
        end

    | Select (t, n, ee) =>
        let
          (* convert from 1-indexing *)
          val i = n-1

          val tee =
            case typOf ee of
              Typ.Prod (ts) =>
                if i >= List.length ts then
                  raise Fail ("ST.refineTyp Select: cannot select component "
                  ^ "#" ^ Int.toString n ^ " on tuple of size "
                  ^ Int.toString (List.length ts))
                else
                  Typ.Prod (List.take (ts, i) @ (t :: List.drop (ts, i+1)))
            | _ => Typ.Unknown

          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Select: expected tuple of type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            case typOf ee' of
              Typ.Prod (ts) =>
                (List.nth (ts, i)
                  handle Subscript =>
                  raise Fail ("ST.refineTyp Select: bug: tuple size"))
            | Typ.Unknown => Typ.Unknown
            | _ => raise Fail ("ST.refineTyp Select: bug")
        in
          { vars = vars
          , exp = Select (Typ.unify (t, t'), n, ee')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Select: unexpected bug in final refine")
          }
        end

    | Ref (t, ee) =>
        let
          val tee =
            case t of
              Typ.Ref (tee) => tee
            | _ => Typ.Unknown

          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Ref: expected type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' = Typ.Ref (typOf ee')
        in
          { vars = vars
          , exp = Ref (Typ.unify (t, t'), ee')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Ref: unexpected bug in final refine")
          }
        end

    | Bang (t, ee) =>
        let
          val tee = Typ.Ref t

          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Bang: expected type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            case typOf ee' of
              Typ.Ref (t') => t'
            | _ => raise Fail ("ST.refineTyp Bang: bug")
        in
          { vars = vars
          , exp = Bang (Typ.unify (t, t'), ee')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Bang: unexpected bug in final refine")
          }
        end

    | Upd (t, e1, e2) =>
        let
          val t1 = Typ.Ref (t)

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Upd: "
                  ^ " in `" ^ toString exp ^ "`"
                  ^ " expected left-hand type "
                  ^ Typ.toString t1 ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val t2 =
            case typOf e1' of
              Typ.Ref (t2) => t2
            | _ => raise Fail ("ST.refineTyp Upd: bug")

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t2
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Upd: "
                  ^ " in `" ^ toString exp ^ "`"
                  ^ " expected right-hand type "
                  ^ Typ.toString t2 ^ " but found "
                  ^ Typ.toString (typOf e2))
              }

          val t' = typOf e2'
        in
          { vars = vars
          , exp = Upd (Typ.unify (t, t'), e1', e2')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Upd: unexpected bug in final refine")
          }
        end

    | Alloc (t, ee) =>
        let
          val tee = Typ.Num

          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Alloc: "
                  ^ " expected type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            Typ.Array (Typ.Unknown)
        in
          { vars = vars
          , exp = Alloc (Typ.unify (t, t'), ee')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Alloc: bug")
          }
        end

    | Length (t, ee) =>
        let
          val tee = Typ.Array (Typ.Unknown)

          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Length: "
                  ^ " expected type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' = Typ.Num
        in
          { vars = vars
          , exp = Length (Typ.unify (t, t'), ee')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Length: bug")
          }
        end

    | ASub (t, e1, e2) =>
        let
          val t1 = Typ.Array (t)

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp ASub: "
                  ^ " expected type "
                  ^ Typ.toString t1 ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val t' =
            case typOf e1' of
              Typ.Array (t') => t'
            | _ => raise Fail ("ST.refineTyp ASub: bug")

          val t2 = Typ.Num

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t2
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp ASub: "
                  ^ " expected type "
                  ^ Typ.toString t2 ^ " but found "
                  ^ Typ.toString (typOf e2))
              }
        in
          { vars = vars
          , exp = ASub (Typ.unify (t, t'), e1', e2')
              handle Overconstrained =>
              raise Fail ("ST.refineType ASub: bug in final refine")
          }
        end

    | AUpd (t, e1, e2, e3) =>
        let
          val t1 = Typ.Array (t)

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp AUpd: "
                  ^ " expected type "
                  ^ Typ.toString t1 ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val t' =
            case typOf e1' of
              Typ.Array (t') => t'
            | _ => raise Fail ("ST.refineTyp AUpd: bug")

          val t2 = Typ.Num

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t2
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp AUpd: "
                  ^ " expected type "
                  ^ Typ.toString t2 ^ " but found "
                  ^ Typ.toString (typOf e2))
              }

          val t3 = t'

          val {vars, exp=e3'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e3 t3
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp AUpd: "
                  ^ " expected type "
                  ^ Typ.toString t3 ^ " but found "
                  ^ Typ.toString (typOf e3))
              }

          val t' = typOf e3'
        in
          { vars = vars
          , exp = AUpd (Typ.unify (t, t'), e1', e2', e3')
              handle Overconstrained =>
              raise Fail ("ST.refineType AUpd: bug in final refine")
          }
        end

    | Array (t, es) =>
        let
          fun refineSubExps vars idx tee ees =
            case ees of
              [] => (vars, tee, [])
            | (ee :: rest) =>
                let
                  val {vars, exp=ee'} =
                    refineTyp
                      { vars = vars
                      , exp = refineRootTyp ee tee
                          handle Overconstrained =>
                          raise Fail ("ST.refineTyp Array: "
                          ^ "expected idx " ^ Int.toString idx
                          ^ " to have type "
                          ^ Typ.toString tee
                          ^ " but found "
                          ^ Typ.toString (typOf ee))
                      }
                  val tee = typOf ee
                  val (vars, tee, rest') = refineSubExps vars (idx+1) tee rest
                in
                  (vars, tee, ee' :: rest')
                end

          val tee =
            case t of
              Typ.Array (x) => x
            | Typ.Unknown => Typ.Unknown
            | _ => raise Fail ("ST.refineTyp Array: bug")

          val (vars, tee', es') = refineSubExps vars 0 tee es

          val t' = Typ.Array (tee')
        in
          { vars = vars
          , exp = Array (Typ.unify (t, t'), es')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Array: bug in final refinement")
          }
        end

    | Seq (t, e1, e2) =>
        let
          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = e1
              }

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Seq: expected type "
                  ^ Typ.toString t ^ " but found "
                  ^ Typ.toString (typOf e2))
              }
        in
          { vars = vars
          , exp = Seq (typOf e2', e1', e2')
          }
        end

    | Let (t, v, e1, e2) =>
        let
          fun updateVarTyp (t1Old, t1New) =
            Typ.unify (t1Old, t1New)
            handle Overconstrained =>
            raise Fail ("ST.refineTyp Let: "
            ^ "expected variable " ^ Id.toString v ^ " to have type "
            ^ Typ.toString t1New ^ " but apparently it has type "
            ^ Typ.toString t1Old)

          val vars = IdTable.insertWith updateVarTyp (v, Typ.Unknown) vars
          val t1 = valOf (IdTable.lookup v vars)

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Let: variable "
                  ^ Id.toString v ^ " has type "
                  ^ Typ.toString t1 ^ " but is bound to expression of type "
                  ^ Typ.toString (typOf e1))
              }

          val vars = IdTable.insertWith updateVarTyp (v, typOf e1') vars

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Let: expected type "
                  ^ Typ.toString t ^ " but found expression of type "
                  ^ Typ.toString (typOf e2))
              }

          val t' = typOf e2'
        in
          { vars = vars
          , exp = Let (Typ.unify (t, t'), v, e1', e2')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Let: bug in final refine")
          }
        end

    | Func (t, func, arg, body) =>
        let
          val (t1, t2) =
            case t of
              Typ.Func (t1, t2) => (t1, t2)
            | _ => (Typ.Unknown, Typ.Unknown)

          val t' = Typ.Func (t1, t2)

          fun updateFuncTyp (tOld, tNew) =
            Typ.unify (tOld, tNew)
            handle Overconstrained =>
            raise Fail ("ST.refineTyp Func: "
            ^ "expected function " ^ Id.toString func ^ " to have type "
            ^ Typ.toString tNew ^ " but apparently it has type "
            ^ Typ.toString tOld)

          val vars = IdTable.insertWith updateFuncTyp (func, t') vars

          val (t1, t2) =
            case valOf (IdTable.lookup func vars) of
              Typ.Func (t1, t2) => (t1, t2)
            | _ => (Typ.Unknown, Typ.Unknown)

          val t' = Typ.Func (t1, t2)

          fun updateArgTyp (t1Old, t1New) =
            Typ.unify (t1Old, t1New)
            handle Overconstrained =>
            raise Fail ("ST.refineTyp Func: "
            ^ "expected argument " ^ Id.toString arg ^ " to have type "
            ^ Typ.toString t1New ^ " but apparently it has type "
            ^ Typ.toString t1Old)

          val vars = IdTable.insertWith updateArgTyp (arg, t1) vars

          val t1 = valOf (IdTable.lookup arg vars)

          val {vars, exp=body'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp body t2
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Func: "
                  ^ "expected body to have type " ^ Typ.toString t2
                  ^ "but found type " ^ Typ.toString (typOf body))
              }

          val t2 = typOf body'

          val t' = Typ.Func (t1, t2)
        in
          { vars = vars
          , exp = Func (Typ.unify (t, t'), func, arg, body')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp Func: bug in final refinement")
          }
        end

    | Op (t, name, f, e1, e2) =>
        let
          val t = Typ.unify (t, Typ.Num)
            handle Overconstrained =>
            raise Fail ("ST.refineTyp Op: expected result type "
            ^ Typ.toString t ^ " but found "
            ^ Typ.toString (Typ.Num))

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 (Typ.Num)
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Op: expected type "
                  ^ Typ.toString (Typ.Num) ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 (Typ.Num)
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp Op: expected type "
                  ^ Typ.toString (Typ.Num) ^ " but found "
                  ^ Typ.toString (typOf e2))
              }
        in
          { vars = vars
          , exp = Op (Typ.Num, name, f, e1', e2')
          }
        end

    | IfZero (t, e1, e2, e3) =>
        let
          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 (Typ.Num)
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp IfZero: expected type "
                  ^ Typ.toString (Typ.Num) ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp IfZero: expected type "
                  ^ Typ.toString t ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e3'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e3 t
                  handle Overconstrained =>
                  raise Fail ("ST.refineTyp IfZero: expected type "
                  ^ Typ.toString t ^ " but found "
                  ^ Typ.toString (typOf e3))
              }
        in
          { vars = vars
          , exp = IfZero (Typ.unify (typOf e2', typOf e3'), e1', e2', e3')
              handle Overconstrained =>
              raise Fail ("ST.refineTyp IfZero: then- and else- branches disagree: "
              ^ " then-branch is type "
              ^ Typ.toString (typOf e2')
              ^ " but else-branch is type "
              ^ Typ.toString (typOf e3'))
          }
        end

  fun inferType (exp: Lang.exp): exp =
    let
      val exp = fromLang exp
      val _ = checkScoping IdSet.empty IdSet.empty exp

      fun loop vars exp =
        let
          val _ = print (IdTable.toString (fn t => " " ^ Typ.toString t ^ "\n") vars ^ "\n")
          val _ = print (toString exp ^ "\n\n")
          val {vars=vars', exp=exp'} =
            refineTyp {vars=vars, exp=exp}
        in
          if equal exp exp' then
            (print ("DONE\n");
            exp)
          else
            loop vars' exp'
        end

      val exp = loop IdTable.empty exp
    in
      if hasUnknowns exp then
        print "WARNING: final type assignment has unknowns\n"
      else
        ();

      exp
    end

end
