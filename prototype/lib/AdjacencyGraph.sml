functor AdjacencyGraph (Vertex: KEY) :
sig
  type t
  type v = Vertex.t
  type e = v * v

  val isEmpty: t -> bool

  val empty: t
  val fromVertices: v list -> t
  val fromEdges: e list -> t
  val vertices: t -> v list
  val edges: t -> e list

  val equal: t * t -> bool
  val toString: t -> string

  val neighbors: v -> t -> v list
  val inNeighbors: v -> t -> v list

  val insertVertex: v -> t -> t
  val insertEdge: e -> t -> t
  val removeVertex: v -> t -> t

  val containsVertex: v -> t -> bool
  val containsEdge: e -> t -> bool

  val isReachableFrom: v -> v -> t -> bool
  val reachableFrom: v -> t -> t

  val transpose: t -> t

  val findSource: t -> v
  val findSink: t -> v

  val decomposeForkJoin: v * v * t -> (v * v * t) list

  val union: t * t -> t
end =
struct

  structure Table = TreeTable (Vertex)
  structure Set = TreeSet (Vertex)

  type v = Vertex.t
  type e = v * v
  type t = v list Table.t

  fun veq (u, v) = (Vertex.compare (u, v) = EQUAL)

  val empty = Table.empty

  fun isEmpty g = Table.size g = 0

  fun equal (g1, g2) =
    Table.equal (fn (n1, n2) => Set.equal (Set.fromList n1, Set.fromList n2))
    (g1, g2)

  fun toString g =
    Table.toString (fn vs => "[" ^ String.concatWith "," (List.map Vertex.toString vs) ^ "]") g

  fun vertices g = Table.keys g
  fun edges g =
    Table.foldr (fn (u, vs, rest) => List.map (fn v => (u, v)) vs @ rest) [] g

  fun neighbors v g =
    case Table.lookup v g of
      NONE => []
    | SOME nbrs => nbrs

  fun insertVertex v g =
    case Table.lookup v g of
      NONE => Table.insert (v, []) g
    | SOME _ => g

  fun insertEdge (u, v) g =
    let
      val g = insertVertex v g
    in
      case Table.lookup u g of
        NONE => Table.insert (u, [v]) g
      | SOME nbrs => Table.insert (u, v :: nbrs) g
    end

  fun removeVertex v g =
    Table.map (List.filter (fn u => not (veq (u, v)))) (Table.remove v g)

  fun containsVertex v g =
    case Table.lookup v g of
      NONE => false
    | SOME _ => true

  fun containsEdge (u, v) g =
    case Table.lookup u g of
      NONE => false
    | SOME nbrs => List.exists (fn x => veq (x, v)) nbrs

  fun fromVertices verts =
    List.foldr (fn (v, g) => insertVertex v g) empty verts

  fun fromEdges edges =
    List.foldr (fn (e, g) => insertEdge e g) empty edges

  fun reachableFrom src (g: t) =
    let
      fun dfs (v, h) =
        if containsVertex v h then
          h
        else
          let val us = neighbors v g
          in List.foldl dfs (Table.insert (v, us) h) us
          end
    in
      dfs (src, Table.empty)
    end

  fun isReachableFrom src dst (g: t) =
    let
      datatype result = FoundIt | Continue of Set.t
      fun dfs (v, vset) =
        if veq (v, dst) then
          FoundIt
        else if Set.member v vset then
          Continue vset
        else
          let
            fun loop nbrs vset =
              case nbrs of
                [] => Continue vset
              | x :: nbrs' =>
                  case dfs (x, vset) of
                    FoundIt => FoundIt
                  | Continue vset' => loop nbrs' vset'
          in
            loop (neighbors v g) (Set.insert v vset)
          end
    in
      case dfs (src, Set.empty) of
        FoundIt => true
      | _ => false
    end

  fun union (g1, g2) = Table.unionWith (fn (vs1, vs2) => vs1 @ vs2) (g1, g2)

  fun transpose g =
    let
      (* clear out the edges *)
      val vertices = Table.map (fn _ => []) g
      (* put them back in, reversed *)
      val edges = fromEdges (List.map (fn (u,v) => (v,u)) (edges g))
    in
      union (vertices, edges)
    end

  fun findSink g =
    case Table.keys (Table.filter (fn vs => List.length vs = 0) g) of
      [v] => v
    | [] => raise Fail "AdjacencyGraph.findSink: no sinks"
    | _ => raise Fail "AdjacencyGraph.findSink: too many sinks"

  fun findSource g =
    findSink (transpose g)

  (* TODO: store in-neighbors map also, to make this more efficient *)
  fun inNeighbors v g =
    neighbors v (transpose g)
    (* Table.keys (Table.filter (List.exists (fn u => veq (u, v))) g) *)

  fun decomposeForkJoin (s, t, g) =
    let
      val childStarts = neighbors s g
      val children = removeVertex s (removeVertex t g)

      fun isolateChild childStart =
        let
          val childGraph = reachableFrom childStart children
          val childSink = findSink childGraph
        in
          (childStart, childSink, childGraph)
        end
    in
      List.map isolateChild childStarts
    end

end
