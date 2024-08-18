/- # De Morgan の法則と排中律

論理和 `∨` と論理積 `∧` の間に次の関係が成立することが知られています。

1. `¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q`
1. `¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q`

これは De Morgan の法則と呼ばれているものの一部です。

## 問1

最初の、論理和の中に否定を入れる方を Lean で証明していきましょう。以下の `sorry` の部分を埋めてください。

`simp` や `rw` でライブラリの命題を引用する方法でも示すことができますし、使わずに自力で示すこともできます。どちらでも構いませんが、Lean に慣れていない人は自力で示すのに挑戦してみてください。
-/

theorem not_or_mp (P Q : Prop) : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q := by
  -- sorry
  -- P ∨ Q が成り立たないと仮定する
  intro (h : ¬ (P ∨ Q))

  -- このとき ¬ P が示せる
  have notP : ¬ P := by
    -- P を仮定すると
    intro hp
    -- P ∨ Q が成り立つ。
    have or : P ∨ Q := Or.inl hp
    -- これは仮定から矛盾
    contradiction

  -- 同様に ¬ Q も示せる
  have notQ : ¬ Q := by
    intro hq
    have or : P ∨ Q := Or.inr hq
    contradiction

  -- したがって `¬ P ∧ ¬ Q` が成り立つ
  exact ⟨notP, notQ⟩
  -- sorry

--##--
-- 別解：ライブラリを使う場合
example (P Q : Prop) : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q := by simp [not_or]
--##--

theorem not_or_mpr (P Q : Prop) : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by
  -- sorry
  -- ¬ P ∧ ¬ Q と仮定する
  intro (h : ¬ P ∧ ¬ Q)

  -- P ∨ Q が成り立つと仮定する
  intro hor

  -- P が成り立つか Q が成り立つかで場合分けする
  rcases hor with hP | hQ

  -- P が成り立つ場合
  case inl =>
    -- これは仮定と矛盾
    exact h.left hP

  -- Q が成り立つ場合
  case inr =>
    -- これも仮定と矛盾
    exact h.right hQ
  -- sorry

--##--
-- 別解：ライブラリを使う場合
example (P Q : Prop) : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by simp [not_or]
--##--

/- ## 問2
次に、論理積の中に否定を入れる方を Lean で証明してみましょう。以下の `sorry` の部分を埋めてください。
-/

theorem not_and_mp (P Q : Prop) : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  -- sorry
  -- ¬ (P ∧ Q) と仮定する
  intro h

  -- P が成り立つか否かで場合分けする
  by_cases hP : P

  -- P が成り立つ場合
  case pos =>
    -- このとき `¬ Q` が成り立つ
    have nQ : ¬ Q := by
      intro hQ
      exact h ⟨hP, hQ⟩

    -- したがって `¬ P ∨ ¬ Q` が成り立つ
    right
    assumption

  -- P が成り立たない場合
  case neg =>
    -- このときは明らかに `¬ P ∨ ¬ Q` が成り立つ
    left
    assumption
  -- sorry

--##--
-- 別解：ライブラリを使う場合
example (P Q : Prop) : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  simp [not_and, Classical.or_iff_not_imp_left]
--##--

theorem not_and_mpr (P Q : Prop) : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
  -- sorry
  -- `¬ P ∨ ¬ Q` と仮定する
  intro h

  -- `P ∧ Q` が成り立つと仮定する
  intro ⟨hP, hQ⟩

  -- 仮定から `¬ P` または `¬ Q` が成り立つが、
  rcases h with hnP | hnQ

  -- どちらの場合でも矛盾する
  all_goals contradiction
  -- sorry

--##--
-- 別解：ライブラリを使う場合
example (P Q : Prop) : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
  simp [not_and, Classical.or_iff_not_imp_left]
--##--

/- ## 問3
問1の命題は、排中律を使わずに示すことができます。問2も、`not_and_mpr` の方は排中律なしで証明できます。

証明で使用した公理を [`#print`](../Command/Diagnostic/Print.md) コマンドで確認してみましょう。排中律を使うと `Classical.choice` という公理が使用されるので、この公理が使われていなければ排中律は使っていません。

ここまでの `not_and_mp` 以外の3つの命題について、排中律をもし使っていたら使わない証明に書き換えてみてください。 -/

--##--
-- この模範解答では、不必要な公理を使用しない方法を紹介している。

/-- info: 'not_or_mp' does not depend on any axioms -/
#guard_msgs in
  #print axioms not_or_mp

/-- info: 'not_or_mpr' does not depend on any axioms -/
#guard_msgs in
  #print axioms not_or_mpr

/-- info: 'not_and_mpr' does not depend on any axioms -/
#guard_msgs in
  #print axioms not_and_mpr
--##--

/- ## 問4
4つの中で唯一排中律が必要だったのは `not_and_mp` です。実はこの命題は、直観主義論理において弱い排中律 `¬ P ∨ ¬ ¬ P` と同値になることが知られています。

これを Lean で証明してみましょう。以下の `sorry` の部分を埋めてください。証明が終わったら、証明が排中律に依存していないことを `#print` コマンドで確認することをお忘れなく。
-/
namespace Playground

/-- de Morgan の法則（論理積の中に否定を入れる） -/
def not_and_mp := ∀ (P Q : Prop), ¬ (P ∧ Q) → ¬ P ∨ ¬ Q

/-- 弱い排中律 -/
def weak_em := ∀ (P : Prop), ¬ P ∨ ¬ ¬ P

/-- カリー化の特殊な場合。証明の中で役に立つかも？ -/
theorem currying (P Q : Prop) : ¬ (P ∧ Q) ↔ (P → ¬ Q) := by
  -- sorry
  have := @not_and P Q
  assumption
  -- sorry

/-- de Morgan の法則（論理積の中に否定を入れる）と弱い排中律が同値 -/
theorem not_and_iff_weak_em : not_and_mp ↔ weak_em := by
  -- sorry
  -- 左方向と右方向をそれぞれ示す
  constructor <;> intro h

  -- 弱い排中律を示す方向
  case mp =>
    -- `P : Prop` が与えられたとする
    intro P

    -- de Morgan の法則に適用すると、
    -- `¬ (P ∧ ¬ P)` を示せばよいことがわかる
    have := h P (¬ P)
    apply this

    -- `P ∧ ¬ P` が成り立つと仮定すると、
    intro ⟨hP, hnP⟩

    -- ただちに矛盾が導かれるので、示すべきことがいえた。
    contradiction

  -- de Morganの法則を示す方向
  case mpr =>
    -- 命題 `P` と `Q` が与えられたとする
    intro P Q

    -- `¬ (P ∧ Q)` が成り立つと仮定する
    intro hand

    -- 仮定の弱い排中律を P と Q に適用する
    have em_p := h P
    have em_q := h Q

    -- これを使って4通りの場合分けをする
    rcases em_p with hnP | hnnP <;> rcases em_q with hnQ | hnnQ

    -- `¬¬ P` かつ `¬¬ Q` の場合以外は、あきらか
    case inl.inl => exact Or.inl hnP
    case inl.inr => exact Or.inl hnP
    case inr.inl => exact Or.inr hnQ

    -- `¬¬ P` かつ `¬¬ Q` の場合は、矛盾を示したい
    exfalso

    -- currying 補題を使って `P → ¬ Q` が得られる
    have := (currying P Q).mp
    replace hand := this hand

    -- よって、¬ P であることがわかる
    replace : ¬ P := by
      -- P だと仮定すると
      intro hP

      -- 仮定から ¬ Q が導かれる
      have nQ : ¬ Q := hand hP

      -- これは矛盾
      contradiction

    -- 仮定から `¬¬ P` なのでこれは矛盾
    contradiction
  -- sorry

-- 使用した公理を確認する
#print axioms not_and_iff_weak_em

--##--
-- 公理に依存していないことを確認している

/-- info: 'Playground.not_and_iff_weak_em' does not depend on any axioms -/
#guard_msgs in
  #print axioms not_and_iff_weak_em
--##--

end Playground
