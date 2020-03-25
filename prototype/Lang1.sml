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
    | Prod of t * t
    | Arr of t * t

    fun toString t =
      case t of
        Unknown => "_"
      | Num => "num"
      | Prod (t1, t2) => toStringP t1 ^ " * " ^ toStringP t2
      | Arr (t1, t2) => toStringP t1 ^ " -> " ^ toStringP t2

    and toStringP t =
      case t of
        Prod _ => parens (toString t)
      | Arr _ => parens (toString t)
      | _ => toString t

    fun equal (t1, t2) =
      case (t1, t2) of
        (Unknown, Unknown) => true
      | (Num, Num) => true
      | (Prod (l1, r1), Prod (l2, r2)) =>
          equal (l1, l2) andalso equal (r1, r2)
      | (Arr (l1, r1), Arr (l2, r2)) =>
          equal (l1, l2) andalso equal (r1, r2)
      | _ => false

    fun hasUnknowns t =
      case t of
        Unknown => true
      | Num => false
      | Prod (t1, t2) => hasUnknowns t1 orelse hasUnknowns t2
      | Arr (t1, t2) => hasUnknowns t1 orelse hasUnknowns t2

    exception Overconstrained

    fun unify (t1, t2) =
      case (t1, t2) of
        (Unknown, Unknown) => Unknown
      | (Num, Num) => Num
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
  | App of typ * exp * exp
  | Par of typ * exp * exp
  | Fst of typ * exp
  | Snd of typ * exp
  | Func of typ * var * var * exp
  | IfZero of typ * exp * exp * exp
  | Num of typ * int
  | Op of typ * string * (int * int -> int) * exp * exp

  fun fold (p as {combine=c: 'a * 'b -> 'b,
                  typ: typ -> 'a,
                  var: var -> 'a,
                  num: int -> 'a})
           (b: 'b)
           (e: exp) =
    case e of
      Var (t, v) => c (var v, c (typ t, b))
    | App (t, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | Par (t, e1, e2) =>
        fold p (fold p (c (typ t, b)) e1) e2
    | Fst (t, e') =>
        fold p (c (typ t, b)) e'
    | Snd (t, e') =>
        fold p (c (typ t, b)) e'
    | Func (t, f, x, e') =>
        fold p (c (var x, c (var f, c (typ t, b)))) e'
    | IfZero (t, e1, e2, e3) =>
        fold p (fold p (fold p (c (typ t, b)) e1) e2) e3
    | Num (t, n) => c (num n, c (typ t, b))
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
    | App (t, _, _) => t
    | Par (t, _, _) => t
    | Fst (t, _) => t
    | Snd (t, _) => t
    | Func (t, _, _, _) => t
    | IfZero (t, _, _, _) => t
    | Num (t, _) => t
    | Op (t, _, _, _, _) => t

  fun OpAdd (e1, e2) = Op (Typ.Num, "+", op+, e1, e2)
  fun OpSub (e1, e2) = Op (Typ.Num, "-", op-, e1, e2)
  fun OpMul (e1, e2) = Op (Typ.Num, "*", op*, e1, e2)

  fun toString e =
    let
      fun withT str =
        case typOf e of
          Typ.Unknown => str
        | t => str ^ " : " ^ Typ.toString t
    in
      case e of
        Var (t, v) => withT (Id.toString v)
      | Num (t, n) => withT (Int.toString n)
      | App (t, e1, e2) =>
          withT (toStringP e1 ^ " " ^ toStringP e2)
      | Par (t, e1, e2) =>
          withT (toStringP e1 ^ " || " ^ toStringP e2)
      | Fst (t, e') =>
          withT (parens ("fst " ^ toStringP e'))
      | Snd (t, e') =>
          withT (parens ("snd " ^ toStringP e'))
      | Func (t, func, arg, body) =>
          withT (parens ("fun " ^ Id.toString func ^ " " ^ Id.toString arg
                         ^ " is " ^ toString body))
      | Op (t, name, _, e1, e2) =>
          withT (parens (toStringP e1 ^ " " ^ name ^ " " ^ toStringP e2))
      | IfZero (t, e1, e2, e3) =>
          withT (parens ("ifz " ^ toString e1 ^ " then " ^ toString e2
                         ^ " else " ^ toString e3))
    end

  and toStringP e = parens (toString e)

  fun canStep e =
    case e of
      Op _ => true
    | App _ => true
    | Par (_, e1, e2) => canStep e1 orelse canStep e2
    | Fst _ => true
    | Snd _ => true
    | IfZero _ => true
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
        Var (t, v) => if Id.eq (v, x) then e' else Var (t, v)
      | App (t, e1, e2) => App (t, doit e1, doit e2)
      | Par (t, e1, e2) => Par (t, doit e1, doit e2)
      | Fst (t, e) => Fst (t, doit e)
      | Snd (t, e) => Snd (t, doit e)
      | Func (t, func, arg, body) => Func (t, func, arg, doit body)
      | Num (t, n) => Num (t, n)
      | Op (t, name, f, e1, e2) => Op (t, name, f, doit e1, doit e2)
      | IfZero (t, e1, e2, e3) => IfZero (t, doit e1, doit e2, doit e3)
    end

  fun tryStep (e: exp): exp =
    case e of
      App (t, e1, e2) =>
        if canStep e1 then
          App (t, tryStep e1, e2)
        else if canStep e2 then
          App (t, e1, tryStep e2)
        else
          let
            val (_, func, arg, body) = deFunc e1
          in
            subst (e1, func) (subst (e2, arg) body)
          end

    | Par (t, e1, e2) =>
        if canStep e1 then
          Par (t, tryStep e1, e2)
        else if canStep e2 then
          Par (t, e1, tryStep e2)
        else
          raise Fail "tryStep Par"

    | Fst (t, e') =>
        if canStep e' then
          Fst (t, tryStep e')
        else
          (case e' of
             Par (_, a, _) => a
           | _ => raise Fail "tryStep Fst")

    | Snd (t, e') =>
        if canStep e' then
          Snd (t, tryStep e')
        else
          (case e' of
             Par (_, _, b) => b
           | _ => raise Fail "tryStep Snd")

    | Op (t, name, f, e1, e2) =>
        if canStep e1 then
          Op (t, name, f, tryStep e1, e2)
        else if canStep e2 then
          Op (t, name, f, e1, tryStep e2)
        else
          let
            val (_, n1) = deNum e1
            val (_, n2) = deNum e2
          in
            Num (t, f (n1, n2))
          end

    | IfZero (t, e1, e2, e3) =>
        if canStep e1 then
          IfZero (t, tryStep e1, e2, e3)
        else
          let
            val (_, n) = deNum e1
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

  (* ========================================================================
   * type checking
   *
   * consists of two parts:
   *   - scope checking (only needs to be done once)
   *   - type inference/refinement
   *)

  fun checkScoping (ctx: IdSet.t) (exp: exp) : unit =
    case exp of
      Num _ => ()
    | Var (_, v) =>
        if not (IdSet.member v ctx) then
          raise Fail ("Lang1.synthType Var: "
                      ^ Id.toString v ^ " not in scope")
        else
          ()
    | App (_, e1, e2) => (checkScoping ctx e1; checkScoping ctx e2)
    | Par (_, e1, e2) => (checkScoping ctx e1; checkScoping ctx e2)
    | Fst (_, e') => checkScoping ctx e'
    | Snd (_, e') => checkScoping ctx e'
    | Func (_, func, arg, body) =>
        let
          val ctx' = IdSet.insert func (IdSet.insert arg ctx)
        in
          checkScoping ctx' body
        end
    | Op (_, _, _, e1, e2) => (checkScoping ctx e1; checkScoping ctx e2)
    | IfZero (_, e1, e2, e3) =>
        (checkScoping ctx e1; checkScoping ctx e2; checkScoping ctx e3)

  val uu = Typ.Unknown

  fun from0 (exp: Lang0.exp): exp =
    case exp of
      Lang0.Num n => Num (uu, n)
    | Lang0.Var v => Var (uu, v)
    | Lang0.App (e1, e2) => App (uu, from0 e1, from0 e2)
    | Lang0.Par (e1, e2) => Par (uu, from0 e1, from0 e2)
    | Lang0.Fst e' => Fst (uu, from0 e')
    | Lang0.Snd e' => Snd (uu, from0 e')
    | Lang0.Func (f, a, b) => Func (uu, f, a, from0 b)
    | Lang0.Op (name, f, e1, e2) => Op (uu, name, f, from0 e1, from0 e2)
    | Lang0.IfZero (e1, e2, e3) =>
        IfZero (uu, from0 e1, from0 e2, from0 e3)

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
    | App (t, e1, e2) => App (Typ.unify (t, t'), e1, e2)
    | Par (t, e1, e2) => Par (Typ.unify (t, t'), e1, e2)
    | Fst (t, e') => Fst (Typ.unify (t, t'), e')
    | Snd (t, e') => Snd (Typ.unify (t, t'), e')
    | Func (t, func, arg, body) => Func (Typ.unify (t, t'), func, arg, body)
    | Op (t, name, f, e1, e2) => Op (Typ.unify (t, t'), name, f, e1, e2)
    | IfZero (t, e1, e2, e3) => IfZero (Typ.unify (t, t'), e1, e2, e3)

  fun refineType {vars: Typ.t IdTable.t, exp: exp}
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
                raise Fail ("Lang1.refineType Var: "
                ^ "expected type " ^ Typ.toString t ^ " but found variable "
                ^ Id.toString v ^ " of type " ^ Typ.toString t')
            in
              {vars = IdTable.insert (v, t'') vars,
               exp = Var (t'', v)}
            end)

    | Num (t, n) =>
        ({vars = vars, exp = Num (Typ.unify (t, Typ.Num), n)}
            handle Typ.Overconstrained =>
            raise Fail ("Lang1.refineType Num: expected type "
            ^ Typ.toString t ^ " but found type " ^ Typ.toString Typ.Num))

    | App (t, e1, e2) =>
        let
          val t1 = Typ.Arr (typOf e2, t)
          val {vars, exp=e1'} =
            refineType
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineType App: expected function of type "
                  ^ Typ.toString t1 ^ " but found " ^ Typ.toString (typOf e1))
              }

          val (t2, t') =
            case typOf e1' of
              Typ.Arr (t2, t') => (t2, t')
            | _ => raise Fail ("Lang1.refineType App: bug in refinement of e1")

          val {vars, exp=e2'} =
            refineType
              { vars = vars
              , exp = refineRootTyp e2 t2
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineType App: function expects argument "
                  ^ "of type " ^ Typ.toString t2 ^ " but found type "
                  ^ Typ.toString (typOf e2))
              }
        in
          { vars = vars
          , exp = App (Typ.unify (t, t'), e1', e2')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineType App: bug in final refinement")
          }
        end

    | Par (t, e1, e2) =>
        let
          val (t1, t2) =
            case t of
              Typ.Prod (t1, t2) => (t1, t2)
            | _ => (Typ.Unknown, Typ.Unknown)

          val {vars, exp=e1'} =
            refineType
              { vars = vars
              , exp = refineRootTyp e1 t1
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineType Par: expected 1st component "
                  ^ "of type " ^ Typ.toString t1 ^ " but found "
                  ^ Typ.toString (typOf e1))
              }

          val {vars, exp=e2'} =
            refineType
              { vars = vars
              , exp = refineRootTyp e2 t2
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineType Par: expected 2nd component "
                  ^ "of type " ^ Typ.toString t2 ^ " but found "
                  ^ Typ.toString (typOf e2))
              }

          val t' = Typ.Prod (typOf e1', typOf e2')
        in
          { vars = vars
          , exp = Par (Typ.unify (t, t'), e1', e2')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineType Par: bug in final refinement")
          }
        end

    | Fst (t, ee) =>
        let
          val tee = Typ.Prod (t, Typ.Unknown)
          val {vars, exp=ee'} =
            refineType
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineType Fst: expected tuple of type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            case typOf ee' of
              Typ.Prod (t', _) => t'
            | _ => raise Fail ("Lang1.refineType Fst: bug")
        in
          { vars = vars
          , exp = Fst (Typ.unify (t, t'), ee')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineType Fst: unexpected bug in final refine")
          }
        end

    | Snd (t, ee) =>
        let
          val tee = Typ.Prod (Typ.Unknown, t)
          val {vars, exp=ee'} =
            refineType
              { vars = vars
              , exp = refineRootTyp ee tee
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineType Snd: expected tuple of type "
                  ^ Typ.toString tee ^ " but found "
                  ^ Typ.toString (typOf ee))
              }

          val t' =
            case typOf ee' of
              Typ.Prod (_, t') => t'
            | _ => raise Fail ("Lang1.refineType Snd: bug")
        in
          { vars = vars
          , exp = Snd (Typ.unify (t, t'), ee')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineType Snd: unexpected bug in final refine")
          }
        end

    | Func (t, func, arg, body) =>
        let
          val (t1, t2) =
            case t of
              Typ.Arr (t1, t2) => (t1, t2)
            | _ => (Typ.Unknown, Typ.Unknown)

          fun updateFuncTyp (t', t) =
            Typ.unify (t', t)
            handle Typ.Overconstrained =>
            raise Fail ("Lang1.refineType Func: "
            ^ "expected function " ^ Id.toString func ^ " to have type "
            ^ Typ.toString t ^ " but apparently it has type "
            ^ Typ.toString t')

          val vars = IdTable.insertWith updateFuncTyp (func, t) vars

          val (t1, t2) =
            case valOf (IdTable.lookup func vars) of
              Typ.Arr (t1, t2) => (t1, t2)
            | _ => (Typ.Unknown, Typ.Unknown)

          fun updateArgTyp (t1', t1) =
            Typ.unify (t1', t1)
            handle Typ.Overconstrained =>
            raise Fail ("Lang1.refineType Func: "
            ^ "expected argument " ^ Id.toString arg ^ " to have type "
            ^ Typ.toString t1 ^ " but apparently it has type "
            ^ Typ.toString t1')

          val vars = IdTable.insertWith updateArgTyp (arg, t1) vars

          val t1 = valOf (IdTable.lookup arg vars)

          val {vars, exp=body'} =
            refineType
              { vars = vars
              , exp = refineRootTyp body t2
                  handle Typ.Overconstrained =>
                  raise Fail ("Lang1.refineType Func: "
                  ^ "expected body to have type " ^ Typ.toString t2
                  ^ "but found type " ^ Typ.toString (typOf body))
              }

          val t2 = typOf body'

          val t' = Typ.Arr (t1, t2)
        in
          { vars = vars
          , exp = Func (Typ.unify (t, t'), func, arg, body')
              handle Typ.Overconstrained =>
              raise Fail ("Lang1.refineType Func: bug in final refinement")
          }
        end

    | Op (t, name, f, e1, e2) =>
        let
          val {vars, exp=e1'} =
            refineType {vars=vars, exp = refineRootTyp e1 Typ.Num}
          val {vars, exp=e2'} =
            refineType {vars=vars, exp = refineRootTyp e2 Typ.Num}
        in
          { vars = vars
          , exp = Op (Typ.unify (t, Typ.Num), name, f, e1', e2')
          }
        end

    | IfZero (t, e1, e2, e3) =>
        let
          val {vars, exp=e1'} =
            refineType {vars=vars, exp = refineRootTyp e1 Typ.Num}
          val {vars, exp=e2'} =
            refineType {vars=vars, exp = refineRootTyp e2 t}
          val {vars, exp=e3'} =
            refineType {vars=vars, exp = refineRootTyp e3 t}
        in
          { vars = vars
          , exp = IfZero (Typ.unify (typOf e2', typOf e3'), e1', e2', e3')
          }
        end

  fun inferType (exp: Lang0.exp): exp =
    let
      val exp = from0 exp
      val _ = checkScoping IdSet.empty exp

      fun loop vars exp =
        let
          val _ = print ("REFINING " ^ toString exp ^ "\n")
          val {vars=vars', exp=exp'} = refineType {vars=vars, exp=exp}
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
