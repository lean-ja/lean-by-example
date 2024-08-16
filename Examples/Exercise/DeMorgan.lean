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
  sorry


theorem not_or_mpr (P Q : Prop) : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by
  sorry


/- ## 問2
次に、論理積の中に否定を入れる方を Lean で証明してみましょう。以下の `sorry` の部分を埋めてください。
-/

theorem not_and_mp (P Q : Prop) : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  sorry


theorem not_and_mpr (P Q : Prop) : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
  sorry


/- ## 問3
問1の命題は、排中律を使わずに示すことができます。問2も、`not_and_mpr` の方は排中律なしで証明できます。

排中律を使うと `Classical.choice` という公理が使用されることを覚えておきましょう。自身の証明で使用した公理を [`#print`](../Command/Diagnostic/Print.md) コマンドで確認して、排中律をもし使っていたら使わない証明に書き換えてみてください。 -/


/- ## 問4
4つの中で唯一排中律が必要だったのは `not_and_mp` ですね。実はこの命題は、直観主義論理において弱い排中律 `¬ P ∨ ¬ ¬ P` と同値になることが知られています。

これを Lean で証明してみましょう。Lean はデフォルトで直観主義論理を採用しているため、Lean で証明をするのは紙とペンで証明するよりも簡単かもしれません。

以下の `sorry` の部分を埋めてください。証明が終わったら、証明が排中律に依存していないことを `#print` コマンドで確認することをお忘れなく。
-/
namespace Playground

/-- de Morgan の法則（論理積の中に否定を入れる） -/
def not_and_mp := ∀ (P Q : Prop), ¬ (P ∧ Q) → ¬ P ∨ ¬ Q

/-- 弱い排中律 -/
def weak_em := ∀ (P : Prop), ¬ P ∨ ¬ ¬ P

/-- カリー化。証明の中で役に立つかも？ -/
theorem currying (P Q : Prop) : ¬ (P ∧ Q) ↔ (P → ¬ Q) := by
  sorry

/-- de Morgan の法則（論理積の中に否定を入れる）と弱い排中律が同値 -/
theorem not_and_iff_weak_em : not_and_mp ↔ weak_em := by
  sorry

-- 使用した公理を確認する
#print axioms not_and_iff_weak_em


end Playground
