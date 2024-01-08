import Mathlib.Tactic --#

/-! # print コマンド -/

/-!
  ## 定義を表示
  `#print` 単体で使うと，定義を表示することができます．
-/

-- inductive Or : Prop → Prop → Prop
-- number of parameters: 2
-- constructors:
-- Or.inl : ∀ {a b : Prop}, a → a ∨ b
-- Or.inr : ∀ {a b : Prop}, b → a ∨ b
#print Or

-- theorem Nat.add_succ : ∀ (n m : ℕ), n + Nat.succ m = Nat.succ (n + m) :=
-- fun n m => rfl
#print Nat.add_succ

/-!
## 依存公理を確認

`#print axioms` で，与えられた証明項が依存する公理を出します．たとえば Lean では排中律は選択原理 `Classical.choice` (選択公理の Lean 版のようなもの)を使って証明するので，排中律は選択原理に依存しています．
-/

/-- 排中律 -/
example : ∀ (p : Prop), p ∨ ¬p := Classical.em

/-- info: 'Classical.em' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in --#
#print axioms Classical.em

/-! また，`sorry` という命題を「証明したことにする」タクティクがありますが，これは `sorryAx` という万能な公理を導入していることが確認できます．-/

theorem contra : False := by sorry

/-- info: 'contra' depends on axioms: [sorryAx] -/
#guard_msgs in --#
#print axioms contra
