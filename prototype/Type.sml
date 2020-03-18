structure Type =
struct

  structure Id = Identifier
  structure IdTable = TreeTable(Id)

  structure StampGraph = AdjacencyGraph(Id)
  fun unions graphs = List.foldr StampGraph.union StampGraph.empty graphs
  type stamp = Id.t

  datatype typ =
    Num
  | Prod of (typ * stamp) * (typ * stamp)
  | Func of (typ * stamp) * (typ * stamp) * (StampGraph.t * stamp * stamp)

  fun sameShape (typ1, typ2) =
    case (typ1, typ2) of
      (Num, Num) => true
    | (Prod ((a, _), (b, _)), Prod ((c, _), (d, _))) =>
        sameShape (a, c) andalso sameShape (b, d)
    | (Func ((a, _), (b, _), _), Func ((c, _), (d, _), _)) =>
        sameShape (a, c) andalso sameShape (b, d)

  type t = typ

  (* returns {ord, typ, stamp, endTime} where
   * expression e has type `typ@stamp`, evaluating between
   * startTime and endTime, and with new allocations `fresh` *)
  fun inferType (ord: StampGraph.t)
                (ctx: (typ * stamp) IdTable.t)
                (e: Lang.exp)
                (startTime: stamp)
              : {fresh: StampGraph.t, typ: typ, stamp: stamp, endTime: stamp} =
    case e of
      Lang.Num _ =>
        { fresh = StampGraph.empty
        , endTime = startTime
        , typ = Num
        , stamp = startTime
        }

    | Lang.Var v =>
        ( case IdTable.lookup v ctx of
            NONE => raise Fail ("T-Var: " ^ Id.toString v ^ " not in scope")
          | SOME (tau, delta) =>
              if StampGraph.reachableFrom delta startTime ord then
                { fresh = StampGraph.empty
                , endTime = startTime
                , typ = tau
                , stamp = delta
                }
              else
                raise Fail ("T-Var: could not establish " ^ Id.toString delta
                            ^ " <= " ^ Id.toString startTime)
        )

    | Lang.Op (name, oper, e1, e2) =>
        let
          val stamp0 = startTime
          val {fresh=fresh1, typ, endTime=stamp1, ...} =
            inferType ord ctx e1 stamp0
          val _ = case typ of Num => () | _ => raise Fail "expected type Num"

          val {fresh=fresh2, typ, endTime=stamp2, ...} =
            inferType (unions [ord, fresh1]) ctx e2 stamp1
          val _ = case typ of Num => () | _ => raise Fail "expected type Num"
        in
          { fresh = unions [fresh1, fresh2]
          , endTime = stamp2
          , typ = Num
          , stamp = stamp2
          }
        end

    | Lang.IfZero (e1, e2, e3) =>
        let
          val stamp0 = startTime
          val {fresh=fresh1, typ, endTime=stamp1, ...} =
            inferType ord ctx e1 stamp0
          val _ = case typ of Num => () | _ => raise Fail "expected type Num"

          val {fresh=fresh2, typ=typThen, stamp=stampThen, endTime=stamp2} =
            inferType (unions [ord, fresh1]) ctx e2 stamp1

          val {fresh=fresh3, typ=typElse, stamp=stampElse, endTime=stamp3} =
            inferType (unions [ord, fresh1]) ctx e3 stamp1
        in
          if not (sameShape (typThen, typElse)) then
            raise Fail ("then and else branch disagree")
          else
            ( TextIO.output (TextIO.stdErr,
                             "WARNING: not sure how to do IfZero; " ^
                             "just taking first branch for now.\n")
            ; { fresh = unions [fresh1, fresh2]
              , endTime = stamp2
              , typ = typThen
              , stamp = stampThen
              }
            )
        end

    | Lang.Par (e1, e2) =>
        let
          val stamp0 = startTime
          val stamp1 = Id.stamp ()
          val stamp2 = Id.stamp ()
          val stamp3 = Id.stamp ()

          val {fresh=fresh1, typ=typLeft, stamp=stampLeft, endTime=stamp1'} =
            inferType (StampGraph.insertEdge (stamp0, stamp1) ord) ctx e1 stamp1

          val {fresh=fresh2, typ=typRight, stamp=stampRight, endTime=stamp2'} =
            inferType (StampGraph.insertEdge (stamp0, stamp2) ord) ctx e2 stamp2

          val newEdges = StampGraph.fromEdges
            [ (stamp0, stamp1), (stamp1', stamp3)
            , (stamp0, stamp2), (stamp2', stamp3)
            ]
        in
          { fresh = unions [newEdges, fresh1, fresh2]
          , endTime = stamp3
          , typ = Prod ((typLeft, stampLeft), (typRight, stampRight))
          , stamp = stamp3
          }
        end

    | _ => raise Fail ("type inference cannot handle expression " ^
                       Lang.toString e)

end
