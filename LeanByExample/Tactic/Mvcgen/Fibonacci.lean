import Lean

open Std.Do

/-- フィボナッチ数列の仕様 -/
@[grind]
def fibSpec (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | k + 2 => fibSpec (k + 1) + fibSpec k

/-- 手続き的に実装された、フィボナッチ数列の実装 -/
def fibImpl (n : Nat) : Nat := Id.run do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  for _i in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

-- `mvcgen` はまだ安定していないという警告を消す
set_option mvcgen.warning false

theorem fibImpl_eq_fibSpec (n : Nat) : fibImpl n = fibSpec n := by
  generalize h : fibImpl n = r
  apply Id.of_wp_run_eq h

  mvcgen invariants
  -- 不変条件の指定
  -- `a` と `b` はループ内で更新される可変変数
  -- `xs.pos` はループの進捗を表していて、いままでにループが回った回数を表す
  · ⇓(xs, ⟨a, b⟩) => ⌜a = fibSpec xs.pos ∧ b = fibSpec (xs.pos + 1)⌝
  with grind
