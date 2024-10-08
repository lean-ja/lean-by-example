/- # gcongr

`gcongr` は合同関係(congruence)を扱うタクティクです。

`n` 変数関数 `f` と `n+1` 個の2項関係 `∼`, `~₁`, ... `∼ₙ` に対して、`x₁ ~₁ x₁' → ... xₙ ~ₙ xₙ' → f x₁ ... xₙ ∼ f x₁' ... xₙ'` が成り立つという形の補題を使って、ゴールを書き換えます。

同様に合同性を扱うタクティクに [`congr`](./Congr.md) がありますが、あちらは等号を扱います。
-/
import Mathlib.Tactic.GCongr -- `gcongr` を使うため
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- `log` を使うため

open Real

variable (a b : ℝ) (x y : ℝ)

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  gcongr

example (h1 : x ≤ y) (h2 : a ≤ b) (h3 : 0 ≤ a) (h4 : 0 ≤ y)
    : x * a ≤ y * b := by
  gcongr

/- `gcongr` はデフォルトでは分解できなくなるまで分解するので、「行き過ぎ」になることがあります。`gcongr` に分解パターンを直接指定することで、行き過ぎを防ぐことができます。-/
set_option linter.unusedTactic false in --#

example {c d : ℝ} (h : a + c + 1 ≤ b + d + 1) :
    x ^ 2 * (a + c) + 5 ≤ x ^ 2 * (b + d) + 5 := by
  -- 単に `gcongr` とすると
  try
    gcongr

    -- 分解が行き過ぎてしまう
    · show a ≤ b

      -- これは証明できない
      fail

  -- 引数でパターンを指定できる
  gcongr x ^ 2 * ?_ + 5

  -- 望ましい分解になった
  show a + c ≤ b + d

  linarith

/- ## 補題の登録
さらに `[gcongr]` 属性を付与することにより、 `gcongr` で呼び出して使える補題を増やすことができます。-/

variable {U : Type*}
variable (A B C : Set U)

/-- 独自に定義した二項関係。中身は `⊆` と同じ。-/
def mysubset (A B : Set U) : Prop := ∀ x, x ∈ A → x ∈ B

/-- `mysubset` を二項関係らしく書けるようにしたもの。-/
infix:50 " ⊆ₘ " => mysubset

example : B ∩ C ⊆ₘ (A ∪ B) ∩ C := by
  -- gcongr が使えない
  fail_if_success gcongr

  intro x hx
  aesop

-- `@[gcongr]` で `gcongr` が使える補題を増やす
@[gcongr]
lemma inter_subset_inter_left (h : A ⊆ B) : A ∩ C ⊆ₘ B ∩ C := by
  intro x hx
  aesop

example : B ∩ C ⊆ₘ (A ∪ B) ∩ C := by
  -- gcongr が使えるようになった
  gcongr

  -- ゴールが変わった
  show B ⊆ A ∪ B
  intro x hx
  aesop
