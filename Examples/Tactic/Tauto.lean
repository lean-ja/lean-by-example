/- # tauto

`tauto` は, トートロジー(恒真式, tautology)であることに基づいてゴールを閉じるタクティクです． ゴールを閉じることができなければエラーになります． -/
import Aesop -- `aesop` を使うため --#
import Mathlib.Tactic.LibrarySearch -- `exact?` を使うため --#
import Mathlib.Tactic.Tauto -- `tauto` を使うのに必要

variable (P Q R : Prop)

-- 含意の導入
example (h : P) : Q → P := by
  tauto

-- フレーゲの3段論法
example : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  tauto

-- 否定と同値なら矛盾
example : (P ↔ ¬ P) → false := by
  tauto

/-! ## tauto の限界
ごく簡単なトートロジーの中にも `tauto` で示せないものがあります．
-/

variable (α : Type) (S : α → Prop)

example : ¬(∀ x, S x) → (∃ x, ¬ S x) := by
  -- `tauto` では示せない
  fail_if_success tauto

  aesop
