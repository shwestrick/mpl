structure Type =
struct

  structure Id = Identifier
  structure IdTable = TreeTable(Id)

  structure StampGraph = AdjacencyGraph(Id)
  fun unions graphs = List.foldr StampGraph.union StampGraph.empty graphs
  type stamp = Id.t

  structure Shape =
  struct
    datatype shape =
      Num
    | Prod of shape * shape
    | Func of shape * shape

    type t = shape
  end

  datatype typ =
    Num
  | Prod of (typ * stamp) * (typ * stamp)
  | Func of (typ * stamp) * (typ * stamp) * (StampGraph.t * stamp * stamp)
  type t = typ

  fun shapeOfTyp typ =
    case typ of
      Num => Shape.Num
    | Prod ((a, _), (b, _)) => Shape.Prod (shapeOfTyp a, shapeOfTyp b)
    | Func ((a, _), (b, _), _) => Shape.Func (shapeOfTyp a, shapeOfTyp b)

  fun sameShape (typ1, typ2) =
    case (typ1, typ2) of
      (Num, Num) => true
    | (Prod ((a, _), (b, _)), Prod ((c, _), (d, _))) =>
        sameShape (a, c) andalso sameShape (b, d)
    | (Func ((a, _), (b, _), _), Func ((c, _), (d, _), _)) =>
        sameShape (a, c) andalso sameShape (b, d)

  (* `extractOrd (typ, anchor) = D` is the same as the judgement
   * the judgement `ord(typ@stamp, anchor) = D` in the paper. *)
  fun extractOrd (typ, stamp, anchor) =
    let
      val newStuff =
        if Id.eq (stamp, anchor) then
          StampGraph.fromVertices [stamp]
        else
          StampGraph.fromEdges [(stamp, anchor)]
    in
      case typ of
        Num => newStuff
      | Func _ => newStuff
      | Prod ((typ1, stamp1), (typ2, stamp2)) =>
          let
            val left = extractOrd (typ1, stamp1, stamp)
            val right = extractOrd (typ2, stamp2, stamp)
          in
            unions [left, right, newStuff]
          end
    end

  (* lift typ@stamp outside of [anchor0, anchor1] with respect to ord *)
  fun liftType (ord, anchor0, anchor1) (typ, stamp) =
    let
      val stamp' =
        if StampGraph.isReachableFrom stamp anchor0 ord then
          stamp
        else
          anchor1
    in
      case typ of
        Num => (typ, stamp')
      | Func _ => (typ, stamp')
      | Prod (p1, p2) =>
          ( Prod ( liftType (ord, anchor0, anchor1) p1
                 , liftType (ord, anchor0, anchor1) p2
                 )
          , stamp'
          )
    end

  (* returns {ord, typ, stamp, endTime} where expression e
   * has type `typ@stamp`, and evaluates between startTime and endTime
   * with new allocations `fresh` *)
  fun inferType (ord: StampGraph.t)
                (ctx: (typ * stamp) IdTable.t)
                (e: Lang0.exp)
                (startTime: stamp)
              : {fresh: StampGraph.t, typ: typ, stamp: stamp, endTime: stamp} =
    case e of
      Lang0.Num _ =>
        { fresh = StampGraph.empty
        , endTime = startTime
        , typ = Num
        , stamp = startTime
        }

    | Lang0.Var v =>
        ( case IdTable.lookup v ctx of
            NONE => raise Fail ("T-Var: " ^ Id.toString v ^ " not in scope")
          | SOME (tau, delta) =>
              if StampGraph.isReachableFrom delta startTime ord then
                { fresh = StampGraph.empty
                , endTime = startTime
                , typ = tau
                , stamp = delta
                }
              else
                raise Fail ("T-Var: could not establish " ^ Id.toString delta
                            ^ " <= " ^ Id.toString startTime)
        )

    | Lang0.Op (name, oper, e1, e2) =>
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

    | Lang0.IfZero (e1, e2, e3) =>
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

    | Lang0.Par (e1, e2) =>
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

    (* | Lang0.Func (func, arg, body) =>
        let
          val extracted = extractOrd
        in
        end *)

    | _ => raise Fail ("type inference cannot handle expression " ^
                       Lang0.toString e)

end
