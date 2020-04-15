(* Lang2 has timestamped types. *)
structure Lang2 =
struct

  fun parens s = "(" ^ s ^ ")"

  structure Id = Identifier
  structure IdTable = TreeTable(Id)
  structure IdSet = TreeSet(Id)
  type var = Id.t

  structure StampGraph = AdjacencyGraph(Id)
  fun unions graphs = List.foldr StampGraph.union StampGraph.empty graphs
  type stamp = Id.t

  (* Types are typ@stamp *)
  structure Typ =
  struct
    datatype t =
      Num of stamp
    | Prod of stamp * t * t
    | Arr of stamp * t * t * (StampGraph.t * stamp * stamp)

    fun toString t =
      case t of
        Num s => "num@" ^ Id.toString s
      | Prod (s, t1, t2) =>
          parens (toString t1 ^ " * " ^ toString t2) ^ "@" ^ Id.toString s
      | Arr (s, t1, t2, (g, top, bot)) =>
          parens (toString t1 ^ " -> " ^ toString t2)
          ^ "[ " ^ Id.toString top ^ ";" ^ Id.toString bot ^ ";"
          ^ StampGraph.toString g ^ "]"
          ^ "@" ^ Id.toString s

    fun stampOf t =
      case t of
        Num s => s
      | Prod (s, _, _) => s
      | Arr (s, _, _, _) => s

    (* `extractOrd (typ, anchor) = D` is the same as the judgement
     * the judgement `ord(typ, anchor) = D` in the paper. *)
    fun extractOrd (typ, anchor) =
      let
        val stamp = stampOf typ
        val newStuff =
          if Id.eq (stamp, anchor) then
            StampGraph.fromVertices [stamp]
          else
            StampGraph.fromEdges [(stamp, anchor)]
      in
        case typ of
          Num _ => newStuff
        | Arr _ => newStuff
        | Prod (_, typ1, typ2) =>
            let
              val left = extractOrd (typ1, stamp)
              val right = extractOrd (typ2, stamp)
            in
              unions [left, right, newStuff]
            end
      end
  end

  type typ = Typ.t

  (* same as Lang0 except nodes have explicit types now *)
  datatype exp =
    Var of typ * var
  | App of typ * exp * exp
  | Par of typ * exp * exp
  | Fst of typ * exp
  | Snd of typ * exp
  | Let of typ * var * exp * exp
  | Func of typ * var * var * exp
  | IfZero of typ * exp * exp * exp
  | Num of typ * int
  | Op of typ * string * (int * int -> int) * exp * exp

  fun typOf e =
    case e of
      Var (t, _) => t
    | App (t, _, _) => t
    | Par (t, _, _) => t
    | Fst (t, _) => t
    | Snd (t, _) => t
    | Let (t, _, _, _) => t
    | Func (t, _, _, _) => t
    | IfZero (t, _, _, _) => t
    | Num (t, _) => t
    | Op (t, _, _, _, _) => t

  fun stampOf e = Typ.stampOf (typOf e)

  fun toString e =
    let
      fun withT str = (str ^ " : " ^ Typ.toString (typOf e))
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
      | Let (t, v, e1, e2) =>
          withT (parens ("let " ^ Id.toString v ^ " = " ^ toString e1 ^ " in "
                         ^ toString e2))
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

  (* Infer the time stamps of a Lang1 expression `exp` with respect to
   * `ord` and `ctx`, producing a Lang2 expression.
   *
   * `exp` evaluates between `startTime` and `endTime`
   * `fresh` are the new allocations of `exp`.
   *)
  fun assignStamps
        {ord: StampGraph.t, ctx: typ IdTable.t, exp: Lang1.exp, startTime: stamp}
      : {fresh: StampGraph.t, exp: exp, endTime: stamp} =
    case exp of
      Lang1.Num (Lang1.Typ.Num, n) =>
        { fresh = StampGraph.empty
        , endTime = startTime
        , exp = Num (Typ.Num startTime, n)
        }

    | Lang1.Var (_, v) =>
        ( case IdTable.lookup v ctx of
            NONE =>
              raise Fail ("Lang2.assignStamps Var: " ^ Id.toString v
                          ^ " not in scope")
          | SOME t =>
              if StampGraph.reachableFrom (Typ.stampOf t) startTime ord then
                { fresh = StampGraph.empty
                , endTime = startTime
                , exp = Var (t, v)
                }
              else
                raise Fail ("Lang2.assignStamps Var: could not establish "
                            ^ Id.toString (Typ.stampOf t) ^ " <= "
                            ^ Id.toString startTime)
        )

    | Lang1.Op (Lang1.Typ.Num, name, oper, e1, e2) =>
        let
          val stamp0 = startTime

          val {fresh=fresh1, endTime=stamp1, exp=e1'} =
            assignStamps {ord=ord, ctx=ctx, startTime=stamp0, exp=e1}

          val {fresh=fresh2, endTime=stamp2, exp=e2'} =
            assignStamps {ord = unions [ord, fresh1],
                          ctx = ctx,
                          startTime = stamp1,
                          exp = e2}
        in
          { fresh = unions [fresh1, fresh2]
          , endTime = stamp2
          , exp = Op (Typ.Num stamp2, name, oper, e1', e2')
          }
        end

    | Lang1.Let (_, v, e1, e2) =>
        let
          val stamp0 = startTime
          val {fresh=fresh1, endTime=stamp1, exp=e1'} =
            assignStamps {ord=ord, ctx=ctx, startTime=stamp0, exp=e1}

          val t1' = typOf e1'

          val {fresh=fresh2, endTime=stamp2, exp=e2'} =
            assignStamps {ord = unions [ord, fresh1],
                          ctx = IdTable.insert (v, t1') ctx,
                          startTime = stamp1,
                          exp = e2}
        in
          { fresh = unions [fresh1, fresh2]
          , endTime = stamp2
          , exp = Let (typOf e2', v, e1', e2')
          }
        end

    | Lang1.Par (_, e1, e2) =>
        let
          val stamp0 = startTime
          val stamp1 = Id.stamp ()
          val stamp2 = Id.stamp ()
          val stamp3 = Id.stamp ()

          val {fresh=fresh1, endTime=stamp1', exp=e1'} =
            assignStamps {ord = StampGraph.insertEdge (stamp0, stamp1) ord,
                          ctx = ctx,
                          startTime = stamp1,
                          exp = e1}

          val {fresh=fresh2, endTime=stamp2', exp=e2'} =
            assignStamps {ord = StampGraph.insertEdge (stamp0, stamp2) ord,
                          ctx = ctx,
                          startTime = stamp2,
                          exp = e2}

          val newEdges = StampGraph.fromEdges
            [ (stamp0, stamp1), (stamp1', stamp3)
            , (stamp0, stamp2), (stamp2', stamp3)
            ]
        in
          { fresh = unions [newEdges, fresh1, fresh2]
          , endTime = stamp3
          , exp = Par (Typ.Prod (stamp3, typOf e1', typOf e2'), e1', e2')
          }
        end

    | Lang1.Fst (_, ee) =>
        let
          val stamp0 = startTime
          val {fresh=fresh, endTime=stamp1, exp=ee'} =
            assignStamps {ord=ord, ctx=ctx, startTime=stamp0, exp=ee}

          val ord' = unions [ord, fresh]

          val t =
            case typOf ee' of
              Typ.Prod (s, t1, t2) =>
                if StampGraph.reachableFrom (Typ.stampOf t1) s ord' then
                  t1
                else
                  raise Fail ("Lang2.assignStamps Fst: cannot establish "
                  ^ Id.toString (Typ.stampOf t1) ^ " <= " ^ Id.toString s
                  ^ " in tuple of type " ^ Typ.toString (typOf ee'))
            | _ =>
                raise Fail ("Lang2.assignStamps Fst: expected tuple but found "
                ^ Typ.toString (typOf ee'))
        in
          { fresh = fresh
          , endTime = stamp1
          , exp = Fst (t, ee')
          }
        end

    | Lang1.Snd (_, ee) =>
        let
          val stamp0 = startTime
          val {fresh=fresh, endTime=stamp1, exp=ee'} =
            assignStamps {ord=ord, ctx=ctx, startTime=stamp0, exp=ee}

          val ord' = unions [ord, fresh]

          val t =
            case typOf ee' of
              Typ.Prod (s, t1, t2) =>
                if StampGraph.reachableFrom (Typ.stampOf t2) s ord' then
                  t2
                else
                  raise Fail ("Lang2.assignStamps Snd: cannot establish "
                  ^ Id.toString (Typ.stampOf t2) ^ " <= " ^ Id.toString s
                  ^ " in tuple of type " ^ Typ.toString (typOf ee'))
            | _ =>
                raise Fail ("Lang2.assignStamps Snd: expected tuple but found "
                ^ Typ.toString (typOf ee'))
        in
          { fresh = fresh
          , endTime = stamp1
          , exp = Snd (t, ee')
          }
        end

    | _ => raise Fail ("Lang2.assignStamps: cannot handle " ^ Lang1.toString exp)

  fun inferType (exp: Lang0.exp) =
    let
      val exp1 = Lang1.inferType exp

      val _ = print "ASSIGNING STAMPS...\n"

      val stamp0 = Id.stamp ()
      val ord0 = StampGraph.fromVertices [stamp0]
      val {fresh=fresh, exp=exp2, endTime=stamp1} =
        assignStamps {ord = ord0,
                      ctx = IdTable.empty,
                      startTime = stamp0,
                      exp = exp1}

      val _ = print (toString exp2 ^ "\n")
      val _ = print ("DONE\n")
    in
      { ord = unions [ord0, fresh]
      , startTime = stamp0
      , endTime = stamp1
      , exp = exp2
      }
    end

end
