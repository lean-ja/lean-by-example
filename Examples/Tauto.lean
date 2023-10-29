import Aesop
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Tauto

variable (P Q R : Prop)

-- ANCHOR: first
-- 含意の導入
example (h : P) : Q → P := by
  tauto

-- フレーゲの3段論法
example : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  tauto

-- 排中律
example : P ∨ ¬ P := by
  -- `aesop` では示すことができない
  try aesop

  tauto

-- 対偶
example (h : P → Q) : ¬ Q → ¬ P := by
  -- `exact?` では示すことができない
  try exact?

  tauto
-- ANCHOR_END: first
