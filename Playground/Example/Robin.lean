import Lean
import Qq

/- # expand_num を simproc でやる例 -/

open Lean Meta Qq

dsimproc_decl unfoldNat ((_)) := fun e => do
  let_expr OfNat.ofNat _ num inst := e | return .continue
  let .lit (.natVal n) := num | return .continue
  let num : Q(Nat) := num
  unless ← withDefault <| isDefEq inst q(instOfNatNat $num) do
    return .continue
  if n ≤ 1 ∨ n > 50 then
    return .done e
  let mut result : Q(Nat) := q(1)
  let mut n := n
  while n > 1 do
    result := q($result + 1)
    n := n - 1
  return .done result

example : 2 + 2 ≠ 5 := by
  dsimp only [unfoldNat]
  decide
