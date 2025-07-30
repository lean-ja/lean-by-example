/- # csimp
`[csimp]` 属性は、コンパイラに単純化を指示します。

`A = B` という形の定理に付与することでコンパイラに `A` の計算を `B` の計算に置き換えさせることができます。非効率な関数を効率的な実装に置き換えるために使用されます。
-/
import Lean

/-- フィボナッチ数列の非効率な実装 -/
def fibonacci : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci n + fibonacci (n+1)

open Lean Elab Command Term Meta in

/-- コマンドが１秒以内に終了することを確かめる -/
elab "#in_second " stx:command : command => do
  let start_time ← IO.monoMsNow
  elabCommand stx
  let end_time ← IO.monoMsNow
  let time := end_time - start_time
  if time ≤ 1000 then
    logInfo m!"time: {time}ms"
  else
    throwError m!"It took more than one second for the command to run."

-- `#eval fibonacci 32` は１秒以上かかる
/-⋆-//-- error: It took more than one second for the command to run. -/
#guard_msgs (error) in --#
#in_second #eval fibonacci 32

/-- フィボナッチ数列のより高速な実装 -/
def fib (n : Nat) : Nat :=
  (loop n).1
where
  -- ヘルパー関数
  loop : Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 =>
      let p := loop n
      (p.2, p.1 + p.2)

/-- `fib` は `fibonacci` と同じ漸化式を満たす -/
theorem fib_add (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := by rfl

/-- `fibonacci` と `fib` は同じ結果を返す。
`[csimp]` 属性を与えることで、`fibonacci` の計算を `fib` の計算に置き換えることができる。-/
@[csimp]
theorem fib_eq_fibonacci : fibonacci = fib := by
  ext n
  induction n using fibonacci.induct
  case case1 => rfl
  case case2 => rfl
  case case3 n ih1 ih2 =>
    rw [fib_add, fibonacci]
    simp [ih1, ih2]

-- `fibonacci` の計算が１秒以内に終わるようになった
#in_second #eval fibonacci 32
#in_second #eval fibonacci 132

/- ## 注意: `[csimp]` 属性による公理の隠蔽

`[csimp]` 属性が付与された定理の証明にどんな公理を使用していようと、それを [`#print axioms`](#{root}/Diagnostic/Print.md#PrintAxioms) で追跡することはできず、[`Lean.ofReduceBool`](#{root}/Declarative/Axiom.md#ofReduceBool) の陰に隠れてしまいます。
-/

def one := 1
def two := 2

/-- 何かの公理 -/
axiom my_axiom : False

@[csimp] theorem one_eq_two : one = two := by
  exact my_axiom.elim

theorem false_theorem : 1 = 2 := by
  rw [show 1 = one from rfl]
  native_decide

-- `my_axiom` に依存しているはずだが、`ofReduceBool` の陰に隠れて見えなくなっている
/-⋆-//-- info: 'false_theorem' depends on axioms: [Lean.ofReduceBool] -/
#guard_msgs in --#
#print axioms false_theorem
