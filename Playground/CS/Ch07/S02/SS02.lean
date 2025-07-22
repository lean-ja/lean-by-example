import Playground.CS.Ch07.S02.SS01
/- ### 7.2.2 Deriving IMP Executions -/

/-- `x := 5; y := x` という代入を続けて行うプログラム -/
def set_to_five : Stmt :=
  assign "x" (fun _ ↦ 5);; assign "y" (fun s ↦ s "x")

/-- `set_to_five` コマンドにより、任意の状態 `s` は `x = 5, y = 5` とセットされた状態に変わる。 -/
example (s : State) : (set_to_five, s) ==> (s["x" ↦ 5]["y" ↦ 5]) := by
  -- set_to_five の定義を展開する
  dsimp [set_to_five]
  big_step
