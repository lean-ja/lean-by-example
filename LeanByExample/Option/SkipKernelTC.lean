/- # debug.skipKernelTC

`debug.skipKernelTC` を有効にすると、カーネルによる型検査が行われなくなります。結果として、不正な証明を Lean に受け入れさせることができてしまいます。
-/
import Lean

section
  open Lean Elab Tactic

  set_option debug.skipKernelTC true

  elab "so_sorry" : tactic => do
    closeMainGoal `so_sorry (Lean.mkConst ``trivial)

  def bad_proof : False := by so_sorry

end

-- Fermat の最終定理が証明できてしまう
theorem easy_proof (x y z n : Nat) : n > 2 → x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
  exact bad_proof.elim

/- `debug.skipKernelTC` を使った証明は、[`#print axioms`](#{root}/Diagnostic/Print.md#PrintAxioms) コマンドを使用しても正当な証明と見分けがつかないことに注意が必要です。 -/

/-⋆-//-- info: 'easy_proof' does not depend on any axioms -/
#guard_msgs in --#
#print axioms easy_proof
