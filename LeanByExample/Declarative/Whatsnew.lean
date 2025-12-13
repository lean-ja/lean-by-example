/- # whatsnew

`whatsnew` コマンドを使うと、あるコマンドによって新たに導入された定理や関数などを見ることができます。
-/

import Mathlib.Util.WhatsNew

/-- 自然数っぽい何か -/
inductive MyNat : Type where
  | zero
  | succ (n : MyNat)

def MyNat.add (m n : MyNat) : MyNat :=
  match m with
  | .zero => n
  | .succ m' => MyNat.succ (MyNat.add m' n)

instance : Add MyNat where
  add := MyNat.add

theorem MyNat.zero_add (n : MyNat) : MyNat.zero + n = n := by
  rfl

/-⋆-//-- info: -- Lean.Meta.simpExtension extension: 1 new entries -/
#guard_msgs in --#
whatsnew in attribute [simp] MyNat.zero_add
