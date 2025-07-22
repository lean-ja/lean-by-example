/- # Problem 56

Let us call a binary tree symmetric if you can draw a vertical line through the root node and then the right subtree is the mirror image of the left subtree. Write a predicate symmetric/1 to check whether a given binary tree is symmetric. Hint: Write a predicate mirror/2 first to check whether one tree is the mirror image of another. We are only interested in the structure, not in the contents of the nodes.
-/

inductive BinTree (α : Type) where
  | empty : BinTree α
  | node : α → BinTree α → BinTree α → BinTree α
deriving Repr

def leaf {α : Type} (a : α) : BinTree α := .node a .empty .empty

/-- This is used to display `#check` results -/
@[app_unexpander BinTree.node]
def leaf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a BinTree.empty BinTree.empty) => `(leaf $a)
  | _ => throw ()

/-- Use `leaf` to display `#eval` results -/
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
