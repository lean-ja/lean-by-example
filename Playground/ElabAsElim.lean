universe u

/-- 標準の再帰子である`Nat.rec`を真似て作った再帰子もどき -/
def Nat.rec' {motive : Nat → Sort u}
    (zero : motive 0) (succ : ∀ n, motive n → motive (n + 1))
    (t : Nat) : motive t := Nat.rec zero succ t

set_option pp.mvars false in

-- 何も付けないとこういうエラーメッセージ
/-⋆-//--
error: Function expected at
  Nat.rec' ?_ (fun x b => b + 1) ?_
but this term has type
  ?_ ?_

Note: Expected a function because this term is being applied to the argument
  a
-/
#guard_msgs in --#
def add (a b : Nat) := Nat.rec' _ (zero := b) (succ := fun _ b => b + 1) a

-- 属性を付与する
attribute [elab_as_elim] Nat.rec'

-- 「eliminatorがエラボレートできません」というエラーメッセージに変わる。
-- eliminatorだと認識されている！
/-⋆-//-- error: failed to elaborate eliminator, expected type is not available -/
#guard_msgs in --#
def add (a b : Nat) := Nat.rec' _ (zero := b) (succ := fun _ b => b + 1) a
