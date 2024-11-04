/- # sorry

証明の細部を埋める前にコンパイルが通るようにしたいとき、証明で埋めるべき箇所に `sorry` と書くとコンパイルが通るようになります。ただし、`sorry` を使用しているという旨の警告が出ます。 -/
import Lean --#

-- Fermat の最終定理
def FermatLastTheorem :=
  ∀ x y z n : Nat, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#guard_msgs (drop warning) in --#
theorem flt : FermatLastTheorem :=
  sorry

/- ## 舞台裏
`Lean.Elab.admitGoal` を使用することで `sorry` と同様のタクティクを作ることができます。
-/

open Lean Elab Tactic

elab "my_sorry" : tactic => withMainContext do
  let goal ← getMainGoal
  admitGoal goal

#guard_msgs (drop warning) in --#
theorem flt' : FermatLastTheorem := by
  my_sorry
