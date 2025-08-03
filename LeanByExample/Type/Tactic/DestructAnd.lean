import Qq
import Batteries

/-- `A₁ ∧ A₂ ∧ ... ∧ Aₙ` という形の前提から `⊢ Aᵢ` を示すタクティク -/
syntax (name := destructAnd) "destruct_and" ident : tactic

open Lean Elab Tactic Qq Meta

/-- 証明項 `hp : Q` が `A₁ ∧ A₂ ∧ ... ∧ Aₙ` の形の命題の証明であるかチェックして、
再帰的に分解して現在のゴールと一致する証明が得られるかを確認し、
もし一致すればゴールを閉じて`true`を返す。一致しなければ`false`を返す。 -/
partial def destructAndExpr (P : Q(Prop)) (hp : Q($P)) : TacticM Bool := withMainContext do
  -- 今証明を構成しようとしている命題を取得
  have target : Q(Prop) := ← getMainTarget

  -- `P` が `target` と一致しているなら、示すべきゴールの証明が得られたことになる。
  if (← isDefEq P target) then
    let goal ← getMainGoal
    goal.assignIfDefEq hp
    return true

  match P with
  | ~q($Q ∧ $R) =>
    let hq : Q($Q) := q(And.left $hp)
    let success ← destructAndExpr Q hq -- 再帰的にチェック
    -- 成功していたら早期リターン
    if success then
      return true

    let hr : Q($R) := q(And.right $hp)
    destructAndExpr R hr -- 再帰的にチェック
  | _ => return false

@[tactic destructAnd]
def evalDestructAnd : Tactic := fun stx => withMainContext do
  match stx with
  | `(tactic| destruct_and $h) =>
    let h ← getFVarFromUserName h.getId
    let success ← destructAndExpr (← inferType h) h
    if !success then
      failure
  | _ => throwUnsupportedSyntax

example (a b c d : Prop) (h : a ∧ b ∧ c ∧ d) : a := by
  destruct_and h

example (a b c d : Prop) (h : a ∧ b ∧ c ∧ d) : b := by
  destruct_and h

example (a b c d : Prop) (h : a ∧ b ∧ c ∧ d) : c := by
  destruct_and h

example (a b c d : Prop) (h : a ∧ b ∧ c ∧ d) : d := by
  destruct_and h

example (a b c : Prop) (h : a ∧ b ∧ c) : a ∧ b := by
  constructor <;> destruct_and h
