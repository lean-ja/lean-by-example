/- # exact?

`exact?` は、カレントゴールを `exact` で閉じることができないか、`import` されているファイル群から検索して提案してくれるタクティクです。閉じることができなければ、エラーになります。-/
import Mathlib.Algebra.Order.Floor.Defs -- `Nat.floor` を使うために必要
import Mathlib.Data.Rat.Floor -- `ℚ` の性質を使うために必要
import Mathlib.Tactic.Says -- `says` を使うために必要

-- `says` のチェックを有効にする --#
set_option says.verify true --#

-- `exact?` はライブラリ検索を行う
example (x : Nat) : x < x + 1 := by
  exact? says
    exact lt_add_one x

-- ローカルコンテキストにある仮定を自動で使ってゴールを導いてくれる
example {P Q R : Prop} (hPQ : P → Q) (hQR : Q → R) (hQ : P) : R := by
  exact? says
    exact (hQR ∘ hPQ) hQ

/- `exact? using h` とするとローカルコンテキストにある仮定 `h` を使用してほしいと明示的に指定することができます。-/

example (n m : Nat) (h1 : n ≠ 0) (_h2 : n > 0) : n * m / n = m := by
  -- `h1` を指定すると `h2` は使わない
  exact? using h1 says
    exact Eq.symm (Nat.eq_div_of_mul_eq_right h1 rfl)

example (n m : Nat) (_h1 : n ≠ 0) (h2 : n > 0) : n * m / n = m := by
  -- `h2` を指定すると `h1` は使わない
  exact? using h2 says
    exact Nat.mul_div_right m h2

/- ## ローカルにある定理の検索

`exact?` は現在の環境にある定理・定数などを読み取るので、ローカルにある定理も検索してくれます。
-/

inductive MyNat where
  | zero
  | succ (n : MyNat)

namespace MyNat

  def add (m n : MyNat) : MyNat :=
    match n with
    | zero => m
    | succ n => succ (add m n)

  -- `+`記号と`0`が使えるようにする
  instance : Add MyNat := ⟨MyNat.add⟩
  instance : Zero MyNat := ⟨MyNat.zero⟩

  theorem add_zero (n : MyNat) : 0 + n = n := by
    induction n
    case zero => rfl
    case succ n ih =>
      rw [show 0 + n.succ = succ (0 + n) from by rfl]
      rw [ih]

  example (n : MyNat) : 0 + n = n := by
    -- 自前で示した定理をちゃんと見つけてくれる
    exact? says
      exact MyNat.add_zero n
end MyNat
/-
## exact? を使用する際のコツ

これは `exact?` に限らず、Lean でライブラリ検索を行うとき常に意識した方が良いことですが、
強すぎる仮定を使用していたり表現が具体的過ぎたりすると上手くいかないことがあります。
適切な抽象化を心掛けてください。
-/

variable (n : ℕ) (a : ℚ)

example (h : ↑ n < a) : n ≤ Nat.floor a := by
  -- ここで単に `exact?` しても通らない
  fail_if_success exact?

  -- 仮定の `<` が強すぎる。
  -- 結論を成り立たせるには `≤` で十分。
  suffices ↑ n ≤ a from by
    -- そうすると `exact?` が通るようになる
    exact? says
      exact Nat.le_floor this

  -- 後は `<` から `≤` を示せばよいだけ
  show ↑n ≤ a
  exact LT.lt.le h
