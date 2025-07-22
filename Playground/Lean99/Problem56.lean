/-
# 問題 56

二分木が「根を通る垂直線で左右の部分木が鏡像関係にある」とき、その木を対称（symmetric）と呼ぶことにする。与えられた二分木が対称かどうか判定する述語 symmetric/1 を実装せよ。ヒント: まず2つの木が鏡像関係かどうか判定する mirror/2 を実装せよ。ノードの内容ではなく構造だけに注目する。
-/

inductive BinTree (α : Type) where
  | empty : BinTree α
  | node : α → BinTree α → BinTree α → BinTree α
deriving Repr

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

variable {α : Type}

def BinTree.mirror (s t : BinTree α) : Bool :=
  match s, t with
  | .empty, .empty => true
  | .node _ a b, .node _ x y => mirror a y && mirror b x
  | _, _ => false

def BinTree.isSymmetric (t : BinTree α) : Bool :=
  match t with
  | .empty => true
  | .node _ l r => mirror l r

#guard BinTree.isSymmetric (leaf 'x')

#guard ! BinTree.isSymmetric (BinTree.node 'x' (leaf 'x') BinTree.empty)

#guard BinTree.isSymmetric (BinTree.node 'x' (leaf 'x') (leaf 'x'))
