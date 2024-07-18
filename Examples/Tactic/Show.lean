/- # show

`show` はこれから示すことを宣言するタクティクです。

* `show ... from` という形で使う場合と、
* `show` 単独で使う場合と

少なくとも2つのパターンがあります。

## 使い捨ての補題を作る

`show ... from` は、[`have`](./Have.md) のように補題を用意することができますが、`have` と違って補題に名前がつかず、使い捨てになります。たとえば `rw` に渡すために一度だけ使いたい補題があるとして、それを `have` で示すのは大げさすぎると感じたときに使用します。 -/
import Mathlib.Tactic.FieldSimp -- `field_simp` を使うのに必要 --#
import Mathlib.Tactic.Ring -- `ring` を使うのに必要 --#

variable (a b x : ℚ)

example (f : ℚ → ℕ) : f ((a + b) ^ 2) = f (a ^ 2 + 2 * a * b + b ^ 2) := by
  -- `have` をつかって補題を用意しなくても、
  -- `show ... from` で無名の証明を構成してそれを `rw` に渡すことができる
  rw [show (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 from by ring]

/-! この話は `show` と直接関係はありませんが、証明項のところに、頭に `?` をつけた変数(メタ変数)を配置すると、証明を後回しにすることができます。 -/

example (h : a * x < b) (ha : a > 0) : x < b / a := by
  -- `b / a` を `r` とおく
  set r := b / a with hr

  -- ここで `b = a * r` というまだ示していない補題に基づいて `h` を書き換える
  rw [show b = a * r from ?lem] at h
  exact (mul_lt_mul_left ha).mp h

  -- 本来証明項が入るべきところに `?lem` をおいたので、
  -- `case lem` でフォーカスできる
  case lem =>
    -- `r` の定義を展開する
    rw [hr]

    -- 分母を払う
    field_simp

/-!
## ゴールの状態を確認する

`show` 単独で使った場合、ゴールが特定の命題に等しいかどうかチェックします。`show P` は, ゴールの中に `⊢ P` (に定義上等しい命題)が存在しないときにエラーになり、存在すればそれをメインのゴールにします。たとえば、証明中にこれから示すべきことを明示し、コードを読みやすくする目的で使うことができます。
-/

variable (P Q : Prop)

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · show P
    exact hP
  · show Q
    exact hQ

/- ゴールを定義上等しい命題に変形するために使用することもできます。-/

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

example : factorial 3 = 6 := by
  -- 定義上等しいのでゴールを変形できる
  show 3 * factorial 2 = 6

  -- 定義上等しいのでゴールを変形できる
  show 3 * (2 * factorial 1) = 6

  rfl
