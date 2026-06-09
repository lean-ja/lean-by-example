/- # irreducible

`[irreducible]` 属性を付与すると、その名前が定義に等しいということが隠されて、[`rfl`](#{root}/Tactic/Rfl.md) タクティクや [`dsimp`](#{root}/Tactic/Dsimp.md) タクティクが通らなくなります。
-/

/-- 階乗関数 -/
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | m + 1 => (m + 1) * factorial m

-- 最初は rfl が通る
example : factorial 5 = 120 := by rfl

/-- info: 6 -/
#guard_msgs in --#
#reduce factorial 3

-- [irreducible]属性を与える
attribute [irreducible] factorial

set_option warn.sorry false in --#
example : factorial 5 = 120 := by
  fail_if_success rfl
  fail_if_success dsimp [factorial]
  sorry

-- `#reduce` は相変わらずできる
/-- info: 6 -/
#guard_msgs in --#
#reduce factorial 3

/- ## reducibility を確認する

Lean が暗黙の裡に `[irreducible]` 属性や `[reducible]` 属性を付与していることがあります。[`#print`](#{root}/Diagnostic/Print.md) コマンドを使うと確認することができます。
-/

def searchF {α : Type} (f : Nat → Option α) (start : Nat) : Option Nat :=
  match f start with
  | some _ => some start
  | none => searchF f (start + 1)
partial_fixpoint

-- `partial_fixpoint` を使ったので irreducible になっている
/--
info: @[irreducible] def searchF : {α : Type} → (Nat → Option α) → Nat → Option Nat :=
fun {α} f =>
  Lean.Order.fix
    (fun f_1 start =>
      match f start with
      | some val => some start
      | none => f_1 (start + 1))
    ⋯
-/
#guard_msgs in --#
#print searchF
