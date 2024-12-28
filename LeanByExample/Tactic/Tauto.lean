/- # tauto

`tauto` は、トートロジー(恒真式、tautology)であることに基づいてゴールを閉じるタクティクです。 ゴールを閉じることができなければエラーになります。 -/
import Aesop -- `aesop` を使うため --#
import Mathlib.Tactic.Tauto -- `tauto` を使うのに必要

section --#

variable (P Q R : Prop)

-- 含意の導入
example (h : P) : Q → P := by
  tauto

-- フレーゲの3段論法
example : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  tauto

-- 否定と同値なら矛盾
example : (P ↔ ¬ P) → False := by
  tauto

end --#
/- `tauto` が扱う対象の「トートロジー」は、命題論理の範囲で記述できるものに限ります。述語論理における恒真な式は、`tauto` で示せないことがあります。-/

example (α : Type) (S : α → Prop) : ¬(∀ x, S x) → (∃ x, ¬ S x) := by
  -- `tauto` では示せない
  fail_if_success tauto

  aesop

example (Q : Prop) : ∀ (P : Prop), P → (Q → P) := by
  -- これは量化子を含むが、`tauto` でも示すことができる。
  tauto

/- ## 排中律

排中律を使わずに示せる命題であっても、`tauto` は排中律を使って示してしまうことがあります。直観主義論理の枠内で命題を示すには、代わりに [`itauto`](./Itauto.md) タクティクを使用してください。-/

/-- 命題とその否定は同値ではない -/
theorem not_neg_iff {P : Prop} : ¬ (P ↔ ¬ P) := by tauto

-- 選択原理を使っているが、これは排中律を使っているため
/-- info: 'not_neg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_neg_iff

-- 実際には排中律は必要ない
theorem not_neg_iff' {P : Prop} : ¬ (P ↔ ¬ P) := by
  intro h
  have hnp : ¬ P := by
    intro hp
    have : ¬ P := by rwa [h] at hp
    contradiction
  have hp : P := by rwa [← h] at hnp
  contradiction

/-- info: 'not_neg_iff'' depends on axioms: [propext] -/
#guard_msgs in #print axioms not_neg_iff'
