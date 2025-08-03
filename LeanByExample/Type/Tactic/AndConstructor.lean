import Qq

/-- ゴールが`P ∧ Q`という形をしていたら、分解してそれぞれ別ゴールにする -/
syntax (name := andConstructor) "and_constructor" : tactic

open Lean Elab Tactic Qq Meta

/-- ゴールが `P ∧ Q` の形をしているかチェックして、
`P ∧ Q` の形をしていたら `P` と `Q` をそれぞれ返す -/
def extracetAndGoals : TacticM (Q(Prop) × Q(Prop)) := do
  have tgt : Q(Prop) := ← getMainTarget -- 右辺でQqを使用していないのでhaveを使う
  match tgt with
  | ~q($p ∧ $q) => return (p, q)
  | _ => throwError "ゴールが `P ∧ Q` の形ではありません。"

@[tactic andConstructor]
def evalAndConstructor : Tactic := fun _stx => withMainContext do
  -- ゴールを取得する
  let goal ← getMainGoal
  have (p, q) := ← extracetAndGoals

  -- 新しいメタ変数（ゴール）を作成する
  have left : Q($p) := ← mkFreshExprSyntheticOpaqueMVar p (tag := `left)
  have right : Q($q) := ← mkFreshExprSyntheticOpaqueMVar q (tag := `right)

  -- ゴールを`?_ ∧ ?_`の形にはめる
  goal.assign q(And.intro $left $right)

  -- アクティブなゴールのリストは自動的には更新されないので、
  -- ２つのゴールを作ったことを宣言する
  replaceMainGoal [left.mvarId!, right.mvarId!]

example : True ∧ True := by
  and_constructor
  · trivial
  · trivial
