structure Type =
struct

  structure Id = Identifier
  type stamp = Id.t

  structure Ctx =
  struct
    type 'a t = (Id.t * 'a) list

    val empty = []
    fun insert ctx (i, x) = (i, x) :: ctx
    fun lookup ctx i =
      case ctx of
        (i', x) :: ctx' => if Id.eq (i, i') then SOME x else lookup ctx' i
      | [] => NONE
  end

  structure Stamp =
  struct
    type t = stamp

    (* adjacency lists *)
    type ord = (stamp * stamp list) list

    fun insert graph stamp = (stamp, []) :: graph

    fun insertPair graph (s1, s2) =
      case graph of
        [] => raise Fail "insertPair but left endpoint doesn't exist"
      | (s, adj) :: graph' =>
          if Id.eq (s1, s) then
            (s, if List.exists (fn t => Id.eq (t, s2)) adj
                then adj
                else s2 :: adj)
          else
            (s, adj) :: insertPair graph' (s1, s2)

    fun contains graph (s1, s2) =
      case graph of
        [] => false
      | (s, adj) :: graph' =>
          if Id.eq (s1, s) then
            List.exists (fn t => Id.eq (t, s2)) adj
          else
            contains graph' (s1, s2)

    fun leq graph (s1, s2) =
      let
      in
      end
  end

  datatype typ =
    Num
  | Func of (typ * stamp) * (typ * stamp) * (Stamp.ord * stamp * stamp)

  type t = typ

  fun inferType (ord: Stamp.ord) (ctx: (typ * stamp) Ctx.t) (e: Lang.exp) (startTime: stamp)
        : {ord: Stamp.ord, typ: typ, stamp: stamp, endTime: stamp} =
    case e of
      Lang.Num _ => {ord = ord, endTime = startTime, typ = Num, stamp = startTime}
    | Lang.Var v =>
        ( case Ctx.lookup ctx v of
            NONE => raise Fail ("T-Var: " ^ Id.toString v ^ " not in scope")
          | SOME (tau, delta) =>
              if Stamp.leq ord (delta, startTime) then
                {ord = ord, endTime = startTime, typ = tau, stamp = delta}
              else
                raise Fail ("T-Var: could not establish " ^ Id.toString delta ^ " <= " Id.toString startTime)
        )
    |



end
