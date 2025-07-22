/- # Problem 50
(Hard 🌟🌟🌟) Huffman codes.

We suppose a set of symbols with their frequencies, given as a list of `fr(S,F)` terms.

Example: `[fr(a,45), fr(b,13), fr(c,12), fr(d,16), fr(e,9), fr(f,5)]`.

Our objective is to construct a list `hc(S,C)` terms, where `C` is the Huffman code word for the symbol `S`.
-/

/-- Insert an element in a way that
does not break the order of the sorted list. -/
def orderedInsert {α : Type} [Ord α] (a : α) : List α → List α
  | [] => [a]
  | b :: l =>
    match compare a b with
    | .lt => a :: b :: l
    | _ => b :: orderedInsert a l

/-- 挿入ソート -/
def insertionSort {α : Type} [Ord α] : List α → List α
  | [] => []
  | b :: l => orderedInsert b (insertionSort l)

-- これを使ってよい
#check insertionSort


/-- Huffman Tree -/
inductive HuffTree where
  | node (left : HuffTree) (right : HuffTree) (weight : Nat)
  | Leaf (c : Char) (weight : Nat)
deriving Inhabited, Repr

def HuffTree.weight : HuffTree → Nat
  | Leaf _ w => w
  | node _ _ w => w

def HuffTree.compare (s s' : HuffTree) : Ordering :=
  let w := s.weight
  let w' := s'.weight
  Ord.compare w w'

instance : Ord HuffTree where
  compare := HuffTree.compare

def HuffTree.sort (trees : List HuffTree) : List HuffTree := insertionSort trees


def String.freq (s : String) (c : Char) := s.data.filter (· == c) |>.length

def String.toLeaves (s : String) : List HuffTree :=
  let allChars : List Char := s.data.eraseDups
  allChars.map fun c => HuffTree.Leaf c (s.freq c)

partial def HuffTree.merge (trees : List HuffTree) : List HuffTree :=
  let sorted := HuffTree.sort trees
  match sorted with
  | [] => []
  | [tree] => [tree]
  | t1 :: t2 :: rest =>
    let t' := HuffTree.node t1 t2 (t1.weight + t2.weight)
    HuffTree.merge (t' :: rest)

-- This function is not used in the solution
def HuffTree.ofString (msg : String) : HuffTree :=
  msg.toLeaves |> HuffTree.merge |>.head!

abbrev Code := String

def HuffTree.encode (c : Char) : HuffTree → Option Code
  | .Leaf c' _ => if c = c' then some "" else none
  | .node l r _w =>
    match l.encode c, r.encode c with
    | none, some s => some ("1" ++ s)
    | some s, none => some ("0" ++ s)
    | _, _ => none


def huffman (input : List (Char × Nat)) : List (Char × Code) :=
  let leaves : List HuffTree := input.map (fun (c, w) => HuffTree.Leaf c w)
  let tree : HuffTree := HuffTree.merge leaves |>.head!
  input.map (fun (c, _) => (c, tree.encode c |>.get!))

#guard huffman [('a', 45),('b', 13),('c', 12),('d', 16),('e', 9),('f', 5)] =
  [('a', "0"),('b', "101"),('c', "100"),('d', "111"),('e', "1101"),('f', "1100")]

#guard huffman [('B', 7),('C', 6),('A', 3),('D', 1),('E', 1),] =
  [('B', "0"), ('C', "11"), ('A', "101"), ('D', "1001"), ('E', "1000")]
