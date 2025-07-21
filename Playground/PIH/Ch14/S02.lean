import Playground.PIH.Ch14.S01

/-- 一般のMonoidに対する畳み込み（構造を壊すような操作） -/
def fold {α : Type} [Monoid α] : List α → α
  | [] => Monoid.unit
  | x :: xs => Monoid.op x (fold xs)

/-- 2分木（空にならない） -/
inductive Tree (a : Type) where
  | leaf (x : a)
  | node (left right : Tree a)

def Tree.fold {a : Type} [Monoid a] : Tree a → a
  | Tree.leaf x => x
  | Tree.node left right => Monoid.op (Tree.fold left) (Tree.fold right)

variable {α β : Type}

class Foldable (t : Type → Type) where
  fold [Monoid α] : t α → α
  foldMap [Monoid β] : (α → β) → t α → β
  foldr : (α → β → β) → β → t α → β
  foldl : (α → β → α) → α → t β → α


