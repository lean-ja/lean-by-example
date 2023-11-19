import Mathlib.Tactic

/-! # print コマンド -/

/-!
  ## print 単体で使う
  -------------------
  `#print` 単体で使うと，定義を表示することができます．
-/

/-
inductive Or : Prop → Prop → Prop
number of parameters: 2
constructors:
Or.inl : ∀ {a b : Prop}, a → a ∨ b
Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/
#print Or

/- theorem Nat.add_succ : ∀ (n m : ℕ), n + Nat.succ m = Nat.succ (n + m) :=
fun n m => rfl -/
#print Nat.add_succ

/-!
  ## print で公理を確認する
  -------------------------
  `#print axioms` で，与えられた証明項が依存する公理を出します．
-/

theorem sor : False := by sorry

-- 'sor' depends on axioms: [sorryAx] と出力される
-- `sorry` で証明すると, `sorryAx` という公理が使われる
#print axioms sor

/- 排中律
Classical.em (p : Prop) : p ∨ ¬p -/
#check Classical.em

-- 'Classical.em' depends on axioms: [Classical.choice, Quot.sound, propext]
-- と出力される．
-- Lean では，排中律は選択原理から導かれているため，
-- Classical.choice が含まれている．
-- 証明の詳細については Diaconescu's theorem を参照のこと．
#print axioms Classical.em
