/- # sorry

証明の細部を埋める前にコンパイルが通るようにしたいとき、証明で埋めるべき箇所に `sorry` と書くとコンパイルが通るようになります。ただし、`sorry` を使用しているという旨の警告が出ます。 -/
import Lean --#

-- Fermat の最終定理
def FermatLastTheorem :=
  ∀ x y z n : Nat, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

/-⋆-//-- warning: declaration uses 'sorry' -/
#guard_msgs (warning) in --#
theorem flt : FermatLastTheorem :=
  sorry

/- ## 補足: sorry 使用の痕跡は隠すことができる

基本的に、`sorry` タクティクを使用すれば `sorryAx` という公理が使用されて、[`#print axioms`](#{root}/Diagnostic/Print.md#PrintAxioms) コマンドの出力に現れるようになります。
-/

/-⋆-//-- info: 'flt' depends on axioms: [sorryAx] -/
#guard_msgs in --#
#print axioms flt

/- しかし、[`[csimp]`](#{root}/Attribute/Csimp.md) 属性を経由することで `sorryAx` を隠し、[`Lean.ofReduceBool`](#{root}/Declarative/Axiom.md#ofReduceBool) の背後に隠してしまうことができます。 -/

def one := 1
def two := 2

#guard_msgs (drop warning) in --#
@[csimp] theorem one_eq_two : one = two := by
  sorry

theorem false_theorem : 1 = 2 := by
  rw [show 1 = one from rfl]
  native_decide

/-⋆-//-- info: 'false_theorem' depends on axioms: [Lean.ofReduceBool] -/
#guard_msgs in --#
#print axioms false_theorem
