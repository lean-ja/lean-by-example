/- # obtain
`obtain` は、分解して何かを得るときに使います。たとえばローカルコンテキストの `h : P ∧ Q` から `hP : P` と `hQ : Q` を取り出したり、`h : ∃ e : X, P e` から `e : X` と `hP : P e` を取り出したりすることができます。

基本的には `obtain <パターン> : 型または命題 := 証明項` という構文で使用します。型は省略することができます。
-/

-- 論理積の分解
example (P Q : Prop) (h : P ∧ Q) : True := by
  obtain ⟨hP, hQ⟩ : P ∧ Q := h

  -- 分解することができた
  guard_hyp hP : P
  guard_hyp hQ : Q

  trivial

-- P は X 上の述語
variable (X : Type) (P : X → Prop)

-- 存在命題の分解
example (h : ∃ e : X, P e) : True := by
  obtain ⟨e, hP⟩ := h

  -- 分解することができた
  guard_hyp e : X
  guard_hyp hP : P e

  trivial

/-
`obtain` に与えることのできるパターンは [`rcases`](./Rcases.md) に与えられるパターンと同様で、一般の[帰納型](#{root}/Declarative/Inductive.md)を分解することができます。
-/

inductive Sample where
  | foo (x y : Nat) : Sample
  | bar (z : String) : Sample

example (s : Sample) : True := by
  obtain ⟨x, y⟩ | ⟨z⟩ := s

  case foo =>
    -- `x`, `y` が取り出せている
    guard_hyp x : Nat
    guard_hyp y : Nat

    trivial
  case bar =>
    -- `z` が取り出せている
    guard_hyp z : String

    trivial
