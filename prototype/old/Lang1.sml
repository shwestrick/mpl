(* Lang1 has basic ML types (type "shapes") but no time stamps *)
structure Lang1 =
struct

  fun parens s = "(" ^ s ^ ")"

  structure Id = Identifier
  structure IdTable = TreeTable(Id)
  structure IdSet = TreeSet(Id)
  type var = Id.t

  (* Types and type constraints coexist. We can express a constraint such as
   * `t = (_ * num -> _)` with Arr (Prod (Unknown, Num), Unknown). Valid typed
   * expressions have no unknowns. *)
  structure Typ =
  struct
    datatype t =
      Unknown
    | Num
    | Ref of t
    | Prod of t * t
    | Arr of t * t

    fun toString t =
      case t of
        Unknown => "_"
      | Num => "num"
      | Ref t => toStringP t ^ " ref"
      | Prod (t1, t2) => toStringP t1 ^ " * " ^ toStringP t2
      | Arr (t1, t2) => toStringP t1 ^ " -> " ^ toStringP t2

    and toStringP t =
      case t of
        Prod _ => parens (toString t)
      | Arr _ => parens (toString t)
      | Ref _ => parens (toString t)
      | _ => toString t

    fun equal (t1, t2) =
      case (t1, t2) of
        (Unknown, Unknown) => true
      | (Num, Num) => true
      | (Ref x1, Ref x2) => equal (x1, x2)
      | (Prod (l1, r1), Prod (l2, r2)) =>
          equal (l1, l2) andalso equal (r1, r2)
      | (Arr (l1, r1), Arr (l2, r2)) =>
          equal (l1, l2) andalso equal (r1, r2)
      | _ => false

    fun hasUnknowns t =
      case t of
        Unknown => true
      | Num => false
      | Ref x => hasUnknowns x
      | Prod (t1, t2) => hasUnknowns t1 orelse hasUnknowns t2
      | Arr (t1, t2) => hasUnknowns t1 orelse hasUnknowns t2

    exception Overconstrained

    fun unify (t1, t2) =
      case (t1, t2) of
        (Unknown, Unknown) => Unknown
      | (Num, Num) => Num
      | (Ref x1, Ref x2) => Ref (unify (x1, x2))
      | (Prod (l1, r1), Prod (l2, r2)) =>
          Prod (unify (l1, l2), unify (r1, r2))
      | (Arr (l1, r1), Arr (l2, r2)) =>
          Arr (unify (l1, l2), unify (r1, r2))
      | (Unknown, _) => t2
      | (_, Unknown) => t1
      | _ => raise Overconstrained
  end

  type typ = Typ.t

  (* same as Lang0 except nodes have explicit types now *)
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

  val uu = Typ.Unknown

  fun from0 (exp: Lang0.exp): exp =
    case exp of
      Lang0.Loc _ => raise Fail ("Lang1 does not have locations")
    | Lang0.Num n => Num (uu, n)
    | Lang0.Var v => Var (uu, v)
    | Lang0.Ref e => Ref (uu, from0 e)
    | Lang0.Bang e => Bang (uu, from0 e)
    | Lang0.Upd (e1, e2) => Upd (uu, from0 e1, from0 e2)
    | Lang0.Seq (e1, e2) => Seq (uu, from0 e1, from0 e2)
    | Lang0.App (e1, e2) => App (uu, from0 e1, from0 e2)
    | Lang0.Par (e1, e2) => Par (uu, from0 e1, from0 e2)
    | Lang0.Fst e' => Fst (uu, from0 e')
    | Lang0.Snd e' => Snd (uu, from0 e')
    | Lang0.Let (v, e1, e2) => Let (uu, v, from0 e1, from0 e2)
    | Lang0.Func (f, a, b) => Func (uu, f, a, from0 b)
    | Lang0.Op (name, f, e1, e2) => Op (uu, name, f, from0 e1, from0 e2)
    | Lang0.IfZero (e1, e2, e3) =>
        IfZero (uu, from0 e1, from0 e2, from0 e3)

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

  fun hasUnknowns e =
    fold {combine = (fn (a, b) => a orelse b),
          typ = Typ.hasUnknowns,
          var = (fn _ => false),
          num = (fn _ => false)}
         false
         e

  fun equal (e1, e2) =
    case (e1, e2) of
      (Var (t1, v1), Var (t2, v2)) =>
        Typ.equal (t1, t2) andalso
        Id.eq (v1, v2)
    | (Num (t1, n1), Num (t2, n2)) =>
        Typ.equal (t1, t2) andalso
        n1 = n2
    | (Ref (t1, x1), Ref (t2, x2)) =>
        Typ.equal (t1, t2) andalso
        equal (x1, x2)
    | (Bang (t1, x1), Bang (t2, x2)) =>
        Typ.equal (t1, t2) andalso
        equal (x1, x2)
    | (Upd (t1, x1, y1), Upd (t2, x2, y2)) =>
        Typ.equal (t1, t2) andalso
        equal (x1, x2) andalso
        equal (y1, y2)
    | (Seq (t1, x1, y1), Seq (t2, x2, y2)) =>
        Typ.equal (t1, t2) andalso
        equal (x1, x2) andalso
        equal (y1, y2)
    | (App (t1, x1, y1), App (t2, x2, y2)) =>
        Typ.equal (t1, t2) andalso
        equal (x1, x2) andalso
        equal (y1, y2)
    | (Par (t1, x1, y1), Par (t2, x2, y2)) =>
        Typ.equal (t1, t2) andalso
        equal (x1, x2) andalso
        equal (y1, y2)
    | (Fst (t1, x1), Fst (t2, x2)) =>
        Typ.equal (t1, t2) andalso
        equal (x1, x2)
    | (Snd (t1, x1), Snd (t2, x2)) =>
        Typ.equal (t1, t2) andalso
        equal (x1, x2)
    | (Let (t1, v1, a1, b1), Let (t2, v2, a2, b2)) =>
        Typ.equal (t1, t2) andalso
        Id.eq (v1, v2) andalso
        equal (a1, a2) andalso
        equal (b1, b2)
    | (Func (t1, f1, a1, b1), Func (t2, f2, a2, b2)) =>
        Typ.equal (t1, t2) andalso
        Id.eq (f1, f2) andalso
        Id.eq (a1, a2) andalso
        equal (b1, b2)
    | (IfZero (t1, a1, b1, c1), IfZero (t2, a2, b2, c2)) =>
        Typ.equal (t1, t2) andalso
        equal (a1, a2) andalso
        equal (b1, b2) andalso
        equal (c1, c2)
    | (Op (t1, n1, _, a1, b1), Op (t2, n2, _, a2, b2)) =>
        Typ.equal (t1, t2) andalso
        n1 = n2 andalso
        equal (a1, a2) andalso
        equal (b1, b2)
    | _ => false

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
          val vStr =
            case typOf e1 of
              Typ.Unknown => Id.toString v
            | t => Id.toString v ^ ": " ^ Typ.toString t
        in
          "let " ^ vStr ^ " = " ^ toString e1 ^ " in " ^ toString e2
        end
    | Func (t, func, arg, body) =>
        let
          val funcStr =
            case t of
              Typ.Unknown => Id.toString func
            | _ => "(" ^ Id.toString func ^ ": " ^ Typ.toString t ^ ")"
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

  (* ========================================================================
   * type checking
   *
   * consists of two parts:
   *   - scope checking (only needs to be done once)
   *   - type inference/refinement
   *)

  fun checkScoping (vars: IdSet.t) (ctx: IdSet.t) (exp: exp) : IdSet.t =
    case exp of
      Num _ => vars
    | Var (_, v) =>
        if not (IdSet.member v ctx) then
          raise Fail ("Lang1.checkScoping Var: "
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
          raise Fail ("Lang1.checkScoping Let: "
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
          raise Fail ("Lang1.checkScoping Func: "
                      ^ Id.toString func ^ " not uniquely bound")
        else if IdSet.member arg vars then
          raise Fail ("Lang1.checkScoping Func: "
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

  (* To implement unification of type constraints on variables, we do multiple
   * passes over the program. We begin by annotating every expression with an
   * unknown type. Then, we thread through a mapping of variables with their
   * constraints, and update this as we gain information. We continue to refine
   * the types of the program until there are no changes.
   *
   * If we ever discover an overconstrained type, we exit.
   *)

  fun refineRootTyp exp t' =
    case exp of
      Var (t, v) => Var (Typ.unify (t, t'), v)
    | Num (t, n) => Num (Typ.unify (t, t'), n)
    | Ref (t, e) => Ref (Typ.unify (t, t'), e)
    | Bang (t, e) => Bang (Typ.unify (t, t'), e)
    | Upd (t, e1, e2) => Upd (Typ.unify (t, t'), e1, e2)
    | Seq (t, e1, e2) => Seq (Typ.unify (t, t'), e1, e2)
    | App (t, e1, e2) => App (Typ.unify (t, t'), e1, e2)
    | Par (t, e1, e2) => Par (Typ.unify (t, t'), e1, e2)
    | Fst (t, e') => Fst (Typ.unify (t, t'), e')
    | Snd (t, e') => Snd (Typ.unify (t, t'), e')
    | Let (t, v, e1, e2) => Let (Typ.unify (t, t'), v, e1, e2)
    | Func (t, func, arg, body) => Func (Typ.unify (t, t'), func, arg, body)
    | Op (t, name, f, e1, e2) => Op (Typ.unify (t, t'), name, f, e1, e2)
    | IfZero (t, e1, e2, e3) => IfZero (Typ.unify (t, t'), e1, e2, e3)

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
                handle Typ.Overconstrained =>
                raise Fail ("Lang1.refineTyp Var: "
                ^ "expected type " ^ Typ.toString t ^ " but found variable "
                ^ Id.toString v ^ " of type " ^ Typ.toString t')
            in
              {vars = IdTable.insert (v, t'') vars,
               exp = Var (t'', v)}
            end)

    | Num (t, n) =>
        ({vars = vars, exp = Num (Typ.unify (t, Typ.Num), n)}
            handle Typ.Overconstrained =>
            raise Fail ("Lang1.refineTyp Num: expected type "
            ^ Typ.toString t ^ " but found type " ^ Typ.toString Typ.Num))

    | App (t, e1, e2) =>
        let
          val t1 = Typ.Arr (typOf e2, t)
          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp App: expected function of type "
                  ^ Typ.toString t1 ^ " but found " ^ Typ.toString (typOf e1))
              }

          val (t2, t') =
            case typOf e1' of
              Typ.Arr (t2, t') => (t2, t')
            | _ => raise Fail ("Lang1.refineTyp App: bug in refinement of e1")

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t2
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp App: function expects argument "
                  ^ "of type " ^ Typ.toString t2 ^ " but found type "
                  ^ Typ.toString (typOf e2))
              }
        in
          { vars = vars
          , exp = App (Typ.unify (t, t'), e1', e2')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineTyp App: bug in final refinement")
          }
        end

    | Par (t, e1, e2) =>
        let
          val (t1, t2) =
            case t of
              Typ.Prod (t1, t2) => (t1, t2)
            | _ => (Typ.Unknown, Typ.Unknown)

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Par: expected 1st component "
                  ^ "of type " ^ Typ.toString t1 ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t2
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Par: expected 2nd component "
                  ^ "of type " ^ Typ.toString t2 ^ " but found "
                  ^ Typ.toString (typOf e2))
              }

          val t' = Typ.Prod (typOf e1', typOf e2')
        in
          { vars = vars
          , exp = Par (Typ.unify (t, t'), e1', e2')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineTyp Par: bug in final refinement")
          }
        end

    | Fst (t, ee) =>
        let
          val tee = Typ.Prod (t, Typ.Unknown)
          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Fst: expected tuple of type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            case typOf ee' of
              Typ.Prod (t', _) => t'
            | _ => raise Fail ("Lang1.refineTyp Fst: bug")
        in
          { vars = vars
          , exp = Fst (Typ.unify (t, t'), ee')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineTyp Fst: unexpected bug in final refine")
          }
        end

    | Snd (t, ee) =>
        let
          val tee = Typ.Prod (Typ.Unknown, t)
          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Snd: expected tuple of type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            case typOf ee' of
              Typ.Prod (_, t') => t'
            | _ => raise Fail ("Lang1.refineTyp Snd: bug")
        in
          { vars = vars
          , exp = Snd (Typ.unify (t, t'), ee')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineTyp Snd: unexpected bug in final refine")
          }
        end

    | Ref (t, ee) =>
        let
          val tee =
            case t of
              Typ.Ref t' => t'
            | _ => Typ.Unknown

          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Ref: expected type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' = Typ.Ref (typOf ee')
        in
          { vars = vars
          , exp = Ref (Typ.unify (t, t'), ee')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineTyp Ref: unexpected bug in final refine")
          }
        end

    | Bang (t, ee) =>
        let
          val tee = Typ.Ref t

          val {vars, exp=ee'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Bang: expected type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            case typOf ee' of
              Typ.Ref t' => t'
            | _ => raise Fail ("Lang1.refineTyp Bang: bug")
        in
          { vars = vars
          , exp = Bang (Typ.unify (t, t'), ee')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineTyp Bang: unexpected bug in final refine")
          }
        end

    | Upd (t, e1, e2) =>
        let
          val t1 = Typ.Ref t

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Upd: "
                  ^ " in `" ^ toString exp ^ "`"
                  ^ " expected left-hand type "
                  ^ Typ.toString t1 ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val t2 =
            case typOf e1' of
              Typ.Ref x => x
            | _ => raise Fail ("Lang1.refineTyp Upd: bug")

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t2
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Upd: "
                  ^ " in `" ^ toString exp ^ "`"
                  ^ " expected right-hand type "
                  ^ Typ.toString t2 ^ " but found "
                  ^ Typ.toString (typOf e2))
              }

          val t' = typOf e2'
        in
          { vars = vars
          , exp = Upd (Typ.unify (t, t'), e1', e2')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineTyp Upd: unexpected bug in final refine")
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
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Seq: expected type "
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
            handle Typ.Overconstrained =>
            raise Fail ("Lang1.refineTyp Let: "
            ^ "expected variable " ^ Id.toString v ^ " to have type "
            ^ Typ.toString t1New ^ " but apparently it has type "
            ^ Typ.toString t1Old)

          val vars = IdTable.insertWith updateVarTyp (v, Typ.Unknown) vars
          val t1 = valOf (IdTable.lookup v vars)

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Let: variable "
                  ^ Id.toString v ^ " has type "
                  ^ Typ.toString t1 ^ " but is bound to expression of type "
                  ^ Typ.toString (typOf e1))
              }

          val vars = IdTable.insertWith updateVarTyp (v, typOf e1') vars

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Let: expected type "
                  ^ Typ.toString t ^ " but found expression of type "
                  ^ Typ.toString (typOf e2))
              }

          val t' = typOf e2'
        in
          { vars = vars
          , exp = Let (Typ.unify (t, t'), v, e1', e2')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineTyp Let: bug in final refine")
          }
        end

    | Func (t, func, arg, body) =>
        let
          val (t1, t2) =
            case t of
              Typ.Arr (t1, t2) => (t1, t2)
            | _ => (Typ.Unknown, Typ.Unknown)

          val t' = Typ.Arr (t1, t2)

          fun updateFuncTyp (tOld, tNew) =
            Typ.unify (tOld, tNew)
            handle Typ.Overconstrained =>
            raise Fail ("Lang1.refineTyp Func: "
            ^ "expected function " ^ Id.toString func ^ " to have type "
            ^ Typ.toString tNew ^ " but apparently it has type "
            ^ Typ.toString tOld)

          val vars = IdTable.insertWith updateFuncTyp (func, t') vars

          val (t1, t2) =
            case valOf (IdTable.lookup func vars) of
              Typ.Arr (t1, t2) => (t1, t2)
            | _ => (Typ.Unknown, Typ.Unknown)

          val t' = Typ.Arr (t1, t2)

          fun updateArgTyp (t1Old, t1New) =
            Typ.unify (t1Old, t1New)
            handle Typ.Overconstrained =>
            raise Fail ("Lang1.refineTyp Func: "
            ^ "expected argument " ^ Id.toString arg ^ " to have type "
            ^ Typ.toString t1New ^ " but apparently it has type "
            ^ Typ.toString t1Old)

          val vars = IdTable.insertWith updateArgTyp (arg, t1) vars

          val t1 = valOf (IdTable.lookup arg vars)

          val {vars, exp=body'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp body t2
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Func: "
                  ^ "expected body to have type " ^ Typ.toString t2
                  ^ "but found type " ^ Typ.toString (typOf body))
              }

          val t2 = typOf body'

          val t' = Typ.Arr (t1, t2)
        in
          { vars = vars
          , exp = Func (Typ.unify (t, t'), func, arg, body')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineTyp Func: bug in final refinement")
          }
        end

    | Op (t, name, f, e1, e2) =>
        let
          val t = Typ.unify (t, Typ.Num)
            handle Typ.Overconstrained =>
            raise Fail ("Lang1.refineTyp Op: expected result type "
            ^ Typ.toString t ^ " but found "
            ^ Typ.toString Typ.Num)

          val {vars, exp=e1'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e1 Typ.Num
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Op: expected type "
                  ^ Typ.toString Typ.Num ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 Typ.Num
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp Op: expected type "
                  ^ Typ.toString Typ.Num ^ " but found "
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
              , exp = refineRootTyp e1 Typ.Num
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp IfZero: expected type "
                  ^ Typ.toString Typ.Num ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e2'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e2 t
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp IfZero: expected type "
                  ^ Typ.toString t ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e3'} =
            refineTyp
              { vars = vars
              , exp = refineRootTyp e3 t
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineTyp IfZero: expected type "
                  ^ Typ.toString t ^ " but found "
                  ^ Typ.toString (typOf e3))
              }
        in
          { vars = vars
          , exp = IfZero (Typ.unify (typOf e2', typOf e3'), e1', e2', e3')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineTyp IfZero: then- and else- branches disagree: "
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
          val {vars=vars', exp=exp'} = refineTyp {vars=vars, exp=exp}
        in
          if equal (exp, exp') then
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
