functor TreeTable (Key: KEY): TABLE =
struct

  structure Key = Key

  datatype 'a t =
    Leaf
  | Node of { key: Key.t
            , value: 'a
            , size: int
            , left: 'a t
            , right: 'a t
            }

  fun size t =
    case t of
      Leaf => 0
    | Node {size, ...} => size

  fun node (l, k, v, r) =
    Node { size = size l + 1 + size r
         , key = k
         , value = v
         , left = l
         , right = r
         }

  val empty = Leaf

  fun singleton (k, v) = node (Leaf, k, v, Leaf)

  fun lookup k t =
    case t of
      Leaf => NONE
    | Node {left, right, key, value, ...} =>
        case Key.compare (k, key) of
          LESS => lookup k left
        | EQUAL => SOME value
        | GREATER => lookup k right

  fun first t =
    case t of
      Leaf => NONE
    | Node {left=Leaf, key, value, ...} => SOME (key, value)
    | Node {left, ...} => first left

  fun last t =
    case t of
      Leaf => NONE
    | Node {right=Leaf, key, value, ...} => SOME (key, value)
    | Node {right, ...} => last right

  fun unsafeJoin (t1, t2) =
    case (t1, t2) of
      (Leaf, _) => t2
    | (_, Leaf) => t1
    | (Node d1, Node d2) =>
        if Key.hash (#key d1) > Key.hash (#key d2) then
          node (#left d1, #key d1, #value d1, unsafeJoin (#right d1, t2))
        else
          node (unsafeJoin (t1, #left d2), #key d2, #value d2, #right d2)

  fun unsafeJoinMid (t1, k, v, t2) =
    case (t1, t2) of
      (Leaf, _) => unsafeJoin (singleton (k, v), t2)
    | (_, Leaf) => unsafeJoin (t1, singleton (k, v))
    | (Node d1, Node d2) =>
        if Key.hash k > Key.hash (#key d1) andalso
           Key.hash k > Key.hash (#key d2)
        then
          node (t1, k, v, t2)
        else if Key.hash (#key d1) > Key.hash (#key d2) then
          node (#left d1, #key d1, #value d1, unsafeJoinMid (#right d1, k, v, t2))
        else
          node (unsafeJoinMid (t1, k, v, #left d2), #key d2, #value d2, #right d2)

  exception Order of Key.t * Key.t

  fun join (t1, t2) =
    case last t1 of
      NONE => t2
    | SOME (k1, _) =>
        case first t2 of
          NONE => t1
        | SOME (k2, _) =>
            case Key.compare (k1, k2) of
              LESS => unsafeJoin (t1, t2)
            | _ => raise Order (k1, k2)

  fun joinMid (t1, k, v, t2) =
    case last t1 of
      NONE => join (singleton (k, v), t2)
    | SOME (k1, _) =>
        if Key.compare (k1, k) <> LESS then raise Order (k1, k) else
        case first t2 of
          NONE => join (t1, singleton (k, v))
        | SOME (k2, _) =>
            if Key.compare (k, k2) <> LESS then raise Order (k, k2)
            else unsafeJoinMid (t1, k, v, t2)

  fun splitAt k t =
    case t of
      Leaf => (Leaf, NONE, Leaf)
    | Node {key, value, left, right, ...} =>
        case Key.compare (k, key) of
          LESS =>
            let val (leftl, b, leftr) = splitAt k left
            in (leftl, b, node (leftr, key, value, right))
            end
        | EQUAL => (left, SOME value, right)
        | GREATER =>
            let val (rightl, b, rightr) = splitAt k right
            in (node (left, key, value, rightl), b, rightr)
            end

  fun insertWith f (k, v) t =
    let
      val (left, mid, right) = splitAt k t
    in
      case mid of
        NONE => joinMid (left, k, v, right)
      | SOME v' => joinMid (left, k, f (v', v), right)
    end

  fun insert (k, v) t = insertWith (fn (old, new) => new) (k, v) t

  fun remove k t =
    let
      val (left, _, right) = splitAt k t
    in
      join (left, right)
    end

  fun unionWith f (t1, t2) =
    case (t1, t2) of
      (Leaf, _) => t2
    | (_, Leaf) => t1
    | (Node {key=k, value=v1, left=l1, right=r1, ...}, _) =>
        let
          val (l2, b, r2) = splitAt k t2
          val v = (case b of NONE => v1 | SOME v2 => f (v1, v2))
          val l = unionWith f (l1, l2)
          val r = unionWith f (r1, r2)
        in
          unsafeJoinMid (l, k, v, r)
        end

  fun union (t1, t2) = unionWith (fn (old, new) => new) (t1, t2)

  fun intersectWith f (t1, t2) =
    case (t1, t2) of
      (Leaf, _) => Leaf
    | (_, Leaf) => Leaf
    | (Node {key=k, value=v1, left=l1, right=r1, ...}, _) =>
        let
          val (l2, b, r2) = splitAt k t2
          val l = intersectWith f (l1, l2)
          val r = intersectWith f (r1, r2)
        in
          case b of
            NONE => unsafeJoin (l, r)
          | SOME v2 => unsafeJoinMid (l, k, f (v1, v2), r)
        end

  fun intersect (t1, t2) = intersectWith (fn (old, new) => new) (t1, t2)

  fun difference (t1, t2) =
    case (t1, t2) of
      (Leaf, _) => Leaf
    | (_, Leaf) => t1
    | (Node {key=k, value=v, left=l1, right=r1, ...}, _) =>
        let
          val (l2, b, r2) = splitAt k t2
          val l = difference (l1, l2)
          val r = difference (r1, r2)
        in
          case b of
            NONE => unsafeJoinMid (l, k, v, r)
          | SOME _ => unsafeJoin (l, r)
        end

  fun foldl f b t =
    case t of
      Leaf => b
    | Node {key, value, left, right, ...} =>
        foldl f (f (key, value, foldl f b left)) right

  fun foldr f b t =
    case t of
      Leaf => b
    | Node {key, value, left, right, ...} =>
        foldr f (f (key, value, foldr f b right)) left

  fun elements t = foldr (fn (k, v, rest) => (k, v) :: rest) [] t
  fun keys t = foldr (fn (k, v, rest) => k :: rest) [] t
  fun values t = foldr (fn (k, v, rest) => v :: rest) [] t

  fun elements t =
    let
      fun loop acc t =
        case t of
          Leaf => acc
        | Node {key, value, left, right, ...} =>
            loop ((key, value) :: loop acc right) left
    in
      loop [] t
    end

  fun toString f t =
    "{" ^
    String.concatWith ","
      (List.map (fn (k, v) => Key.toString k ^ ":" ^ f v) (elements t))
    ^ "}"

  fun check t =
    let
      datatype keyinf = PosInf | NegInf | K of Key.t
      fun less (k1, k2) =
        case (k1, k2) of
          (K kk1, K kk2) => (Key.compare (kk1, kk2) = LESS)
        | (K _, PosInf) => true
        | (NegInf, K _) => true
        | _ => false

      fun sweep (k1, k2) prio t =
        case t of
          Leaf => true
        | Node {key, left, right, size=n, ...} =>
            n = size left + size right + 1 andalso
            less (k1, K key) andalso
            less (K key, k2) andalso
            Key.hash key <= prio andalso
            sweep (k1, K key) (Key.hash key) left andalso
            sweep (K key, k2) (Key.hash key) right
    in
      sweep (NegInf, PosInf) (valOf Int.maxInt) t
    end

  fun mapk f t =
    case t of
      Leaf => Leaf
    | Node {key, value, left, right, ...} =>
        node (mapk f left, key, f (key, value), mapk f right)

  fun map f t = mapk (fn (_, v) => f v) t

  fun filterk f t =
    case t of
      Leaf => Leaf
    | Node {key, value, left, right, ...} =>
        if f (key, value) then
          node (filterk f left, key, value, filterk f right)
        else
          unsafeJoin (filterk f left, filterk f right)

  fun filter f t = filterk (fn (_, v) => f v) t

end
