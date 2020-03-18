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
            inferType (StampGraph.union (ord, fresh1)) ctx e2 stamp1
          val _ = case typ of Num => () | _ => raise Fail "expected type Num"
        in
          { fresh = StampGraph.union (fresh1, fresh2)
          , endTime = stamp2
          , typ = Num
          , stamp = stamp2
          }
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

          val newEdges =
            [ (stamp0, stamp1), (stamp1', stamp3)
            , (stamp0, stamp2), (stamp2', stamp3)
            ]
        in
          { fresh = unions [StampGraph.fromEdges newEdges, fresh1, fresh2]
          , endTime = stamp3
          , typ = Prod ((typLeft, stampLeft), (typRight, stampRight))
          , stamp = stamp3
          }
        end

    | _ => raise Fail ("type inference cannot handle expression " ^
                       Lang.toString e)

end
