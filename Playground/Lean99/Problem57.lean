/-
# 問題 57

講義第4章で開発した add/3 を使って、整数リストから二分探索木を構成する述語を実装せよ。
-/

inductive BinTree (α : Type) where
  | empty : BinTree α
  | node : α → BinTree α → BinTree α → BinTree α

def leaf {α : Type} (a : α) : BinTree α := .node a .empty .empty

/-- #check の結果表示用 -/
@[app_unexpander BinTree.node]
def leaf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a BinTree.empty BinTree.empty) => `(leaf $a)
  | _ => throw ()

/-- #eval の結果表示用 -/
def BinTree.toString {α : Type} [ToString α] (t : BinTree α) : String :=
  match t with
  | .node v .empty .empty => s!"leaf {v}"
  | .node v l r => s!"BinTree.node {v} ({toString l}) ({toString r})"
  | .empty => "empty"

instance {α : Type} [ToString α] : ToString (BinTree α) := ⟨BinTree.toString⟩

variable {α : Type}

instance [Ord α] : Max α where
  max x y :=
    match compare x y with
    | .lt => y
    | _ => x

def BinTree.max [Ord α] (t : BinTree α) : Option α :=
  match t with
  | .empty => none
  | .node v l r =>
    let left_max := (max l).getD v
    let right_max := (max r).getD v
    some <| [left_max, right_max].foldl Max.max v

def BinTree.searchTree [Ord α] (t : BinTree α) : Bool :=
  match t with
  | .empty => true
  | .node v l r =>
    let left_max := (max l).getD v
    let right_max := (max r).getD v
    match compare left_max v, compare v right_max with
    | _, .gt => false
    | .gt, _ => false
    | _, _ => searchTree l && searchTree r

def BinTree.searchTreeFromList [Ord α] (xs : List α) : BinTree α :=
  xs.foldl insert BinTree.empty
where
  insert : BinTree α → α → BinTree α
  | .empty, x => leaf x
  | .node v l r, x =>
    match compare x v with
    | .lt => BinTree.node v (insert l x) r
    | _ => BinTree.node v l (insert r x)

#guard BinTree.node 3 (.node 2 (leaf 1) .empty) (.node 5 .empty (leaf 7)) |>.searchTree

#guard BinTree.searchTreeFromList [3, 2, 5, 7, 1] |>.searchTree
