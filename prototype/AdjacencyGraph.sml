functor AdjacencyGraph (Vertex: KEY) :
sig
  type t
  type v = Vertex.t
  type e = v * v

  val empty: t
  val fromVertices: v list -> t
  val fromEdges: e list -> t
  val vertices: t -> v list
  val edges: t -> e list

  val toString: t -> string

  val neighbors: v -> t -> v list

  val insertVertex: v -> t -> t
  val insertEdge: e -> t -> t

  val containsVertex: v -> t -> bool
  val containsEdge: e -> t -> bool

  val reachableFrom: v -> v -> t -> bool

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

  fun reachableFrom src dst (g: t) =
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

end
