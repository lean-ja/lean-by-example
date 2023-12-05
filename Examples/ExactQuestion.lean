import Mathlib.Algebra.Order.Floor -- `Nat.floor` を使うために必要
import Mathlib.Data.Rat.Floor -- `ℚ` の性質を使うために必要
import Mathlib.Tactic.LibrarySearch -- `exact?` を使うのに必要
import Mathlib.Tactic.Says -- `says` を使うために必要

variable (P Q R : Prop)

/-! ## exact? -/

-- `exact?` はライブラリ検索を行う
example (x : Nat) : x < x + 1 := by
  -- `Try this: exact Nat.lt.base x` と出力される
  exact?

-- ローカルコンテキストにある仮定を自動で使ってゴールを導いてくれる
example (hPQ : P → Q) (hQR : Q → R) (hQ : P) : R := by
  -- `Try this: exact hQR (hPQ hQ)` と出力される
  exact?

  -- 証明は `exact?` だけで終わっている
  done

/-!
  ## exact? を使用する際のコツ

  これは `exact?` に限らず, Lean でライブラリ検索を行うとき
  常に意識した方が良いことですが
  強すぎる仮定を使用していたり
  表現が具体的過ぎたりすると上手くいかないことがあります.
  適切な抽象化を心掛けてください．
-/

variable (n : ℕ) (a : ℚ)

example (h : ↑ n < a) : n ≤ Nat.floor a := by
  -- ここで単に `exact?` しても通らない
  try exact?

  -- 仮定の `<` が強すぎる．
  -- 結論を成り立たせるには `≤` で十分．
  suffices ↑ n ≤ a from by
    -- そうすると `exact?` が通るようになる
    exact? says
      exact Nat.le_floor this

  -- 後は `<` から `≤` を示せばよいだけ
  show ↑n ≤ a
  exact? says
    exact le_of_lt h
