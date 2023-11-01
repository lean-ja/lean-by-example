import Aesop
import Mathlib.Tactic.LibrarySearch -- `exact?` を使うため
import Mathlib.Tactic.Tauto -- `tauto` を使うのに必要

variable (P Q R : Prop)

/-! ## tauto -/

-- 含意の導入
example (h : P) : Q → P := by
  tauto

-- フレーゲの3段論法
example : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  tauto

/-! ## aesop との比較 -/

variable (α : Type) (S : α → Prop)

-- 排中律
example : P ∨ ¬ P := by
  -- `aesop` では示すことができない
  try aesop

  tauto

example : ¬(∀ x, S x) → (∃ x, ¬ S x) := by
  -- `tauto` では示せない
  try tauto

  aesop

/-! ## exact? との比較 -/

-- 対偶
example (h : P → Q) : ¬ Q → ¬ P := by
  -- `exact?` では示すことができない
  try exact?

  tauto
