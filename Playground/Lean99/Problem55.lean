/-
# 問題 55
(中級 🌟🌟) 完全平衡二分木を構成せよ。

完全平衡二分木では、すべてのノードについて「左部分木と右部分木のノード数の差が1以下」という性質が成り立つ。

与えられたノード数に対して、すべての完全平衡二分木を構成する関数 `cbalTree` を実装せよ。すべての解をバックトラックで生成すること。

> **注意**
>
> 完全平衡二分木は（高さ）平衡二分木とは異なる。
-/

inductive BinTree (α : Type) where
  | empty : BinTree α
  | node : α → BinTree α → BinTree α → BinTree α
deriving Repr

def leaf {α : Type} (a : α) : BinTree α := .node a .empty .empty

def BinTree.nodes {α : Type} : BinTree α → Nat
| .empty => 0
| .node _ l r => 1 + l.nodes + r.nodes

def BinTree.isCBalanced {α : Type} : BinTree α → Bool
  | .empty => true
  | .node _ l r =>
    Int.natAbs ((l.nodes : Int) - (r.nodes : Int)) ≤ 1 && l.isCBalanced && r.isCBalanced

namespace ListMonad

/-- List型のモナドインスタンス -/
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

end ListMonad

open scoped ListMonad

/-- ノード数が `x` の完全平衡二分木をすべて構成する -/
partial def cbalTree (x : Nat) : List (BinTree Unit) :=
  match x with
  | 0 => [.empty]
  | n + 1 => do
    let q := n / 2
    let r := n % 2
    let indices := List.range (q+r+1) |>.drop q
    let i ← indices
    let left ← cbalTree i
    let right ← cbalTree (n - i)
    pure (BinTree.node () left right)

#eval (cbalTree 3).length = 1
#eval (cbalTree 3)|>.map BinTree.isCBalanced |>.and
#eval (cbalTree 4)|>.map BinTree.isCBalanced |>.and
#eval (cbalTree 4).length = 4
#eval (cbalTree 5)|>.map BinTree.isCBalanced |>.and
#eval (cbalTree 6)|>.map BinTree.isCBalanced |>.and
#eval (cbalTree 7).length = 1
