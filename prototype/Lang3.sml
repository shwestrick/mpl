(* Lang3 has depthed types with subtyping.
 * Derived from Lang3. *)
structure Lang3 =
struct

  fun parens s = "(" ^ s ^ ")"

  structure Id = Identifier
  structure IdTable = TreeTable(Id)
  structure IdSet = TreeSet(Id)
  type var = Id.t

  structure Typ =
  struct
    type depth = int
    type d = depth

    datatype t =
      Top
    | Bot
    | Num of d
    | Ref of d * t
    | GRef of d * t
    | SRef of d * t
    | Prod of d * t * t
    | Arr of d * t * t

    fun toString t =
      case t of
        Top => "?"
      | Bot => "!!"
      | Num d => "num@" ^ Int.toString d
      | Ref (d, t) => toString t ^ " ref@" ^ Int.toString d
      | GRef (d, t) => toString t ^ " gref@" ^ Int.toString d
      | SRef (d, t) => toString t ^ " sref@" ^ Int.toString d
      | Prod (d, t1, t2) =>
          parens (toString t1 ^ " * " ^ toString t2) ^ "@" ^ Int.toString d
      | Arr (d, t1, t2) =>
          parens (toString t1 ^ " -> " ^ toString t2) ^ "@" ^ Int.toString d

    fun depthOf t =
      case t of
        Num d => d
      | Ref (d, _) => d
      | GRef (d, _) => d
      | SRef (d, _) => d
      | Prod (d, _, _) => d
      | Arr (d, _, _) => d
      | _ => raise Fail ("Lang3.Typ.depthOf: " ^ toString t)

    fun equal x y =
      case (x, y) of
        (Top, Top) => true
      | (Bot, Bot) => true
      | (Num d, Num d') => d = d'
      | (Ref (d, t), Ref (d', t')) => d = d' andalso equal t t'
      | (GRef (d, t), GRef (d', t')) => d = d' andalso equal t t'
      | (SRef (d, t), SRef (d', t')) => d = d' andalso equal t t'
      | (Prod (d, t1, t2), Prod (d', t1', t2')) =>
          d = d' andalso equal t1 t1' andalso equal t2 t2'
      | (Arr (d, t1, t2), Arr (d', t1', t2')) =>
          d = d' andalso equal t1 t1' andalso equal t2 t2'
      | _ => false

    fun hasBots ty =
      case ty of
        Bot => true
      | Ref (d, t) => hasBots t
      | GRef (d, t) => hasBots t
      | SRef (d, t) => hasBots t
      | Prod (d, t1, t2) => hasBots t1 orelse hasBots t2
      | Arr (d, t1, t2) => hasBots t1 orelse hasBots t2
      | _ => false

    fun hasTops ty =
      case ty of
        Top => true
      | Ref (d, t) => hasTops t
      | GRef (d, t) => hasTops t
      | SRef (d, t) => hasTops t
      | Prod (d, t1, t2) => hasTops t1 orelse hasTops t2
      | Arr (d, t1, t2) => hasTops t1 orelse hasTops t2
      | _ => false

    fun min d d' = Int.min (d, d')
    fun max d d' = Int.max (d, d')

    fun capAt d' ty =
      case ty of
        Top => Top
      | Bot => Bot
      | Num d => Num (min d d')
      | Ref (d, t) => Ref (min d d', capAt d' t)
      | GRef (d, t) => GRef (min d d', capAt d' t)
      | SRef (d, t) => SRef (min d d', capAt d' t)
      | Prod (d, t1, t2) => Prod (min d d', capAt d' t1, capAt d' t2)
      | Arr (d, t1, t2) => Arr (min d d', capAt d' t1, capAt d' t2)

    fun leq x y = equal x (glb x y)

    and glb x y =
      case (x, y) of
        (Num d, Num d') => Num (min d d')

      | (Ref (d, t), Ref (d', t')) =>
          if equal t t' then Ref (min d d', t) else Bot
      | (Ref (d, t), GRef (d', t')) => Ref (min d d', glb t t')
      | (Ref (d, t), SRef (d', t')) => Ref (min d d', lub t t')

      | (GRef _, Ref _) => glb y x
      | (GRef (d, t), GRef (d', t')) => GRef (min d d', glb t t')
      | (GRef (d, t), SRef (d', t')) =>
          if equal t t' then Ref (min d d', t) else Bot

      | (SRef _, Ref _) => glb y x
      | (SRef _, GRef _) => glb y x
      | (SRef (d, t), SRef (d', t')) => SRef (min d d', lub t t')

      | (Arr (d, t1, t2), Arr (d', t1', t2')) =>
          Arr (min d d', lub t1 t1', glb t2 t2')

      | (Prod (d, t1, t2), Prod (d', t1', t2')) =>
          Prod (min d d', glb t1 t1', glb t2 t2')

      | (Top, _) => y

      | (_, Top) => x

      | _ => Bot

    and lub x y =
      case (x, y) of
        (Num d, Num d') => Num (max d d')

      | (Ref (d, t), Ref (d', t')) =>
          if equal t t' then
            Ref (max d d', t)
          else if leq t t' then
            GRef (max d d', t')
          else if leq t' t then
            SRef (max d d', t)
          else
            Top
      | (Ref (d, t), GRef (d', t')) => GRef (max d d', lub t t')
      | (Ref (d, t), SRef (d', t')) => SRef (max d d', glb t t')

      | (GRef _, Ref _) => lub y x
      | (GRef (d, t), GRef (d', t')) => GRef (max d d', lub t t')

      | (SRef _, Ref _) => lub y x
      | (SRef (d, t), SRef (d', t')) => SRef (max d d', glb t t')

      | (Arr (d, t1, t2), Arr (d', t1', t2')) =>
          Arr (max d d', glb t1 t1', lub t2 t2')

      | (Prod (d, t1, t2), Prod (d', t1', t2')) =>
          Prod (max d d', lub t1 t1', lub t2 t2')

      | (Bot, _) => y

      | (_, Bot) => x

      | _ => Top

    fun unify (t1, t2) = glb t1 t2

  end

  type typ = Typ.t

  datatype exp =
    Var of typ * var
  | Num of typ * int
  | Ref of typ * exp
  | Upd of typ * exp * exp
  | Bang of typ * exp
  | Seq of typ * exp * exp
  | App of typ * exp * exp
  | Par of typ * exp * exp
  | Fst of typ * exp
  | Snd of typ * exp
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
    | Seq (t, _, _) => t
    | App (t, _, _) => t
    | Par (t, _, _) => t
    | Fst (t, _) => t
    | Snd (t, _) => t
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
    | App (_, e1, e2) =>
        toStringP e1 ^ " " ^ toStringP e2
    | Seq (_, e1, e2) =>
        toStringP e1 ^ "; " ^ toStringP e2
    | Par (_, e1, e2) =>
        toStringP e1 ^ " || " ^ toStringP e2
    | Fst (_, e') => "fst " ^ toStringP e'
    | Snd (_, e') => "snd " ^ toStringP e'
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

  val tt = Typ.Top

  fun from0 (exp: Lang0.exp): exp =
    case exp of
      Lang0.Loc _ => raise Fail ("Lang3 does not have locations")
    | Lang0.Num n => Num (tt, n)
    | Lang0.Var v => Var (tt, v)
    | Lang0.Ref e => Ref (tt, from0 e)
    | Lang0.Bang e => Bang (tt, from0 e)
    | Lang0.Upd (e1, e2) => Upd (tt, from0 e1, from0 e2)
    | Lang0.Seq (e1, e2) => Seq (tt, from0 e1, from0 e2)
    | Lang0.App (e1, e2) => App (tt, from0 e1, from0 e2)
    | Lang0.Par (e1, e2) => Par (tt, from0 e1, from0 e2)
    | Lang0.Fst e' => Fst (tt, from0 e')
    | Lang0.Snd e' => Snd (tt, from0 e')
    | Lang0.Let (v, e1, e2) => Let (tt, v, from0 e1, from0 e2)
    | Lang0.Func (f, a, b) => Func (tt, f, a, from0 b)
    | Lang0.Op (name, f, e1, e2) => Op (tt, name, f, from0 e1, from0 e2)
    | Lang0.IfZero (e1, e2, e3) =>
        IfZero (tt, from0 e1, from0 e2, from0 e3)

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
    | Seq (t, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | App (t, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | Par (t, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | Fst (t, e') =>
        fold p (c (typ t, b)) e'
    | Snd (t, e') =>
        fold p (c (typ t, b)) e'
    | Let (t, v, e1, e2) =>
        fold p (fold p (c (var v, c (typ t, b))) e1) e2
    | Func (t, f, x, e') =>
        fold p (c (var x, c (var f, c (typ t, b)))) e'
    | IfZero (t, e1, e2, e3) =>
        fold p (fold p (fold p (c (typ t, b)) e1) e2) e3
    | Op (t, _, _, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2

  fun hasTops e =
    fold {combine = (fn (a, b) => a orelse b),
          typ = Typ.hasTops,
          var = (fn _ => false),
          num = (fn _ => false)}
         false
         e

  fun hasBots e =
    fold {combine = (fn (a, b) => a orelse b),
          typ = Typ.hasBots,
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
    | (Seq (t1, x1, y1), Seq (t2, x2, y2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (App (t1, x1, y1), App (t2, x2, y2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (Par (t1, x1, y1), Par (t2, x2, y2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2 andalso
        equal y1 y2
    | (Fst (t1, x1), Fst (t2, x2)) =>
        Typ.equal t1 t2 andalso
        equal x1 x2
    | (Snd (t1, x1), Snd (t2, x2)) =>
        Typ.equal t1 t2 andalso
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
          raise Fail ("Lang3.checkScoping Var: "
                      ^ Id.toString v ^ " not in scope")
        else
          vars
    | Ref (_, e) =>
        checkScoping vars ctx e
    | Bang (_, e) =>
        checkScoping vars ctx e
    | Upd (_, e1, e2) =>
        checkScoping (checkScoping vars ctx e1) ctx e2
    | Seq (_, e1, e2) =>
        checkScoping (checkScoping vars ctx e1) ctx e2
    | App (_, e1, e2) =>
        checkScoping (checkScoping vars ctx e1) ctx e2
    | Par (_, e1, e2) =>
        checkScoping (checkScoping vars ctx e1) ctx e2
    | Fst (_, e) =>
        checkScoping vars ctx e
    | Snd (_, e) =>
        checkScoping vars ctx e
    | Let (_, v, e1, e2) =>
        if IdSet.member v vars then
          raise Fail ("Lang3.checkScoping Let: "
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
          raise Fail ("Lang3.checkScoping Func: "
                      ^ Id.toString func ^ " not uniquely bound")
        else if IdSet.member arg vars then
          raise Fail ("Lang3.checkScoping Func: "
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
    case exp of
      Var (t, v) => Var (Typ.glb t t', v)
    | Num (t, n) => Num (Typ.glb t t', n)
    | Ref (t, e) => Ref (Typ.glb t t', e)
    | Bang (t, e) => Bang (Typ.glb t t', e)
    | Upd (t, e1, e2) => Upd (Typ.glb t t', e1, e2)
    | Seq (t, e1, e2) => Seq (Typ.glb t t', e1, e2)
    | App (t, e1, e2) => App (Typ.glb t t', e1, e2)
    | Par (t, e1, e2) => Par (Typ.glb t t', e1, e2)
    | Fst (t, e') => Fst (Typ.glb t t', e')
    | Snd (t, e') => Snd (Typ.glb t t', e')
    | Let (t, v, e1, e2) => Let (Typ.glb t t', v, e1, e2)
    | Func (t, func, arg, body) => Func (Typ.glb t t', func, arg, body)
    | Op (t, name, f, e1, e2) => Op (Typ.glb t t', name, f, e1, e2)
    | IfZero (t, e1, e2, e3) => IfZero (Typ.glb t t', e1, e2, e3)

  exception Overconstrained

  val refineRootTyp = (fn exp => fn t =>
    let
      val exp' = refineRootTyp exp t
    in
      case typOf exp' of
        Typ.Bot => raise Overconstrained
      | _ => exp'
    end)

  fun refineTyp {vars: Typ.t IdTable.t, depth: int, exp: exp}
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
                raise Fail ("Lang3.refineTyp Var: "
                ^ "expected type " ^ Typ.toString t ^ " but found variable "
                ^ Id.toString v ^ " of type " ^ Typ.toString t')
            in
              {vars = IdTable.insert (v, t'') vars,
               exp = Var (t'', v)}
            end)

    | Num (t, n) =>
        ({vars = vars, exp = Num (Typ.unify (t, Typ.Num depth), n)}
            handle Overconstrained =>
            raise Fail ("Lang3.refineTyp Num: expected type "
            ^ Typ.toString t ^ " but found type "
            ^ Typ.toString (Typ.Num depth)))

    | App (t, e1, e2) =>
        let
          val t1 = Typ.Arr (depth, typOf e2, t)
          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e1 t1
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp App: expected function of type "
                  ^ Typ.toString t1 ^ " but found " ^ Typ.toString (typOf e1))
              }

          val (t2, t') =
            case typOf e1' of
              Typ.Arr (_, t2, t') => (t2, t')
            | _ => raise Fail ("Lang3.refineTyp App: bug in refinement of e1")

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e2 t2
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp App: function expects argument "
                  ^ "of type " ^ Typ.toString t2 ^ " but found type "
                  ^ Typ.toString (typOf e2))
              }
        in
          { vars = vars
          , exp = App (Typ.unify (t, t'), e1', e2')
              handle Overconstrained =>
              raise Fail ("Lang3.refineTyp App: bug in final refinement")
          }
        end

    | Par (t, e1, e2) =>
        let
          val (t1, t2) =
            case t of
              Typ.Prod (_, t1, t2) => (t1, t2)
            | _ => (Typ.Top, Typ.Top)

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , depth = depth + 1
              , exp = refineRootTyp e1 t1
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Par: expected 1st component "
                  ^ "of type " ^ Typ.toString t1 ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , depth = depth + 1
              , exp = refineRootTyp e2 t2
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Par: expected 2nd component "
                  ^ "of type " ^ Typ.toString t2 ^ " but found "
                  ^ Typ.toString (typOf e2))
              }

          val t' = Typ.Prod
            ( depth
            , Typ.capAt depth (typOf e1')
            , Typ.capAt depth (typOf e2')
            )
        in
          { vars = vars
          , exp = Par (Typ.unify (t, t'), e1', e2')
              handle Overconstrained =>
              raise Fail ("Lang3.refineTyp Par: bug in final refinement")
          }
        end

    | Fst (t, ee) =>
        let
          val tee = Typ.Prod (depth, t, Typ.Top)
          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp ee tee
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Fst: expected tuple of type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            case typOf ee' of
              Typ.Prod (_, t', _) => t'
            | _ => raise Fail ("Lang3.refineTyp Fst: bug")
        in
          { vars = vars
          , exp = Fst (Typ.unify (t, t'), ee')
              handle Overconstrained =>
              raise Fail ("Lang3.refineTyp Fst: unexpected bug in final refine")
          }
        end

    | Snd (t, ee) =>
        let
          val tee = Typ.Prod (depth, Typ.Top, t)
          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp ee tee
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Snd: expected tuple of type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            case typOf ee' of
              Typ.Prod (_, _, t') => t'
            | _ => raise Fail ("Lang3.refineTyp Snd: bug")
        in
          { vars = vars
          , exp = Snd (Typ.unify (t, t'), ee')
              handle Overconstrained =>
              raise Fail ("Lang3.refineTyp Snd: unexpected bug in final refine")
          }
        end

    | Ref (t, ee) =>
        let
          val tee =
            case t of
              Typ.Ref (_, t') => t'
            | _ => Typ.Top

          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp ee tee
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Ref: expected type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' = Typ.Ref (depth, typOf ee')
        in
          { vars = vars
          , exp = Ref (Typ.unify (t, t'), ee')
              handle Overconstrained =>
              raise Fail ("Lang3.refineTyp Ref: unexpected bug in final refine")
          }
        end

    | Bang (t, ee) =>
        let
          val tee = Typ.GRef (depth, t)

          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp ee tee
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Bang: expected type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            case typOf ee' of
              Typ.Ref (_, t') => t'
            | Typ.GRef (_, t') => t'
            | _ => raise Fail ("Lang3.refineTyp Bang: bug")
        in
          { vars = vars
          , exp = Bang (Typ.unify (t, t'), ee')
              handle Overconstrained =>
              raise Fail ("Lang3.refineTyp Bang: unexpected bug in final refine")
          }
        end

    | Upd (t, e1, e2) =>
        let
          val t1 = Typ.SRef (depth, t)

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e1 t1
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Upd: "
                  ^ " in `" ^ toString exp ^ "`"
                  ^ " expected left-hand type "
                  ^ Typ.toString t1 ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val t2 =
            case typOf e1' of
              Typ.SRef (_, x) => x
            | Typ.Ref (_, x) => x
            | _ => raise Fail ("Lang3.refineTyp Upd: bug: "
                   ^ "found expression `" ^ toString e1' ^ "`"
                   ^ " of type " ^ Typ.toString (typOf e1')
                   ^ " but expected either sref or ref")

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e2 t2
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Upd: "
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
              raise Fail ("Lang3.refineTyp Upd: unexpected bug in final refine")
          }
        end

    | Seq (t, e1, e2) =>
        let
          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = e1
              }

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e2 t
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Seq: expected type "
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
            raise Fail ("Lang3.refineTyp Let: "
            ^ "expected variable " ^ Id.toString v ^ " to have type "
            ^ Typ.toString t1New ^ " but apparently it has type "
            ^ Typ.toString t1Old)

          val vars = IdTable.insertWith updateVarTyp (v, Typ.Top) vars
          val t1 = valOf (IdTable.lookup v vars)

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e1 t1
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Let: variable "
                  ^ Id.toString v ^ " has type "
                  ^ Typ.toString t1 ^ " but is bound to expression of type "
                  ^ Typ.toString (typOf e1))
              }

          val vars = IdTable.insertWith updateVarTyp (v, typOf e1') vars

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e2 t
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Let: expected type "
                  ^ Typ.toString t ^ " but found expression of type "
                  ^ Typ.toString (typOf e2))
              }

          val t' = typOf e2'
        in
          { vars = vars
          , exp = Let (Typ.unify (t, t'), v, e1', e2')
              handle Overconstrained =>
              raise Fail ("Lang3.refineTyp Let: bug in final refine")
          }
        end

    | Func (t, func, arg, body) =>
        let
          val (t1, t2) =
            case t of
              Typ.Arr (_, t1, t2) => (t1, t2)
            | _ => (Typ.Top, Typ.Top)

          val t' = Typ.Arr (depth, t1, t2)

          fun updateFuncTyp (tOld, tNew) =
            Typ.unify (tOld, tNew)
            handle Overconstrained =>
            raise Fail ("Lang3.refineTyp Func: "
            ^ "expected function " ^ Id.toString func ^ " to have type "
            ^ Typ.toString tNew ^ " but apparently it has type "
            ^ Typ.toString tOld)

          val vars = IdTable.insertWith updateFuncTyp (func, t') vars

          val (t1, t2) =
            case valOf (IdTable.lookup func vars) of
              Typ.Arr (_, t1, t2) => (t1, t2)
            | _ => (Typ.Top, Typ.Top)

          val t' = Typ.Arr (depth, t1, t2)

          fun updateArgTyp (t1Old, t1New) =
            Typ.unify (t1Old, t1New)
            handle Overconstrained =>
            raise Fail ("Lang3.refineTyp Func: "
            ^ "expected argument " ^ Id.toString arg ^ " to have type "
            ^ Typ.toString t1New ^ " but apparently it has type "
            ^ Typ.toString t1Old)

          val vars = IdTable.insertWith updateArgTyp (arg, t1) vars

          val t1 = valOf (IdTable.lookup arg vars)

          val {vars, exp=body'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp body t2
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Func: "
                  ^ "expected body to have type " ^ Typ.toString t2
                  ^ "but found type " ^ Typ.toString (typOf body))
              }

          val t2 = typOf body'

          val t' = Typ.Arr (depth, t1, t2)
        in
          { vars = vars
          , exp = Func (Typ.unify (t, t'), func, arg, body')
              handle Overconstrained =>
              raise Fail ("Lang3.refineTyp Func: bug in final refinement")
          }
        end

    | Op (t, name, f, e1, e2) =>
        let
          val t = Typ.unify (t, Typ.Num depth)
            handle Overconstrained =>
            raise Fail ("Lang3.refineTyp Op: expected result type "
            ^ Typ.toString t ^ " but found "
            ^ Typ.toString (Typ.Num depth))

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e1 (Typ.Num depth)
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Op: expected type "
                  ^ Typ.toString (Typ.Num depth) ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e2 (Typ.Num depth)
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp Op: expected type "
                  ^ Typ.toString (Typ.Num depth) ^ " but found "
                  ^ Typ.toString (typOf e2))
              }
        in
          { vars = vars
          , exp = Op (Typ.Num depth, name, f, e1', e2')
          }
        end

    | IfZero (t, e1, e2, e3) =>
        let
          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e1 (Typ.Num depth)
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp IfZero: expected type "
                  ^ Typ.toString (Typ.Num depth) ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e2 t
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp IfZero: expected type "
                  ^ Typ.toString t ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e3'} =
            refineTyp
              { vars = vars
              , depth = depth
              , exp = refineRootTyp e3 t
                  handle Overconstrained =>
                  raise Fail ("Lang3.refineTyp IfZero: expected type "
                  ^ Typ.toString t ^ " but found "
                  ^ Typ.toString (typOf e3))
              }
        in
          { vars = vars
          , exp = IfZero (Typ.unify (typOf e2', typOf e3'), e1', e2', e3')
              handle Overconstrained =>
              raise Fail ("Lang3.refineTyp IfZero: then- and else- branches disagree: "
              ^ " then-branch is type "
              ^ Typ.toString (typOf e2')
              ^ " but else-branch is type "
              ^ Typ.toString (typOf e3'))
          }
        end

  fun inferType (exp: Lang0.exp): exp =
    let
      val exp = from0 exp
      val _ = checkScoping IdSet.empty IdSet.empty exp

      fun loop vars exp =
        let
          val _ = print ("REFINING " ^ toString exp ^ "\n")
          val {vars=vars', exp=exp'} =
            refineTyp {vars=vars, depth=0, exp=exp}
        in
          if equal exp exp' then
            (print ("DONE\n");
            exp)
          else
            loop vars' exp'
        end

      val exp = loop IdTable.empty exp
    in
      if hasTops exp then
        print "WARNING: final type assignment has unknowns\n"
      else
        ();

      exp
    end

end
