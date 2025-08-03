import Qq

/-- ゴールが`P ↔ Q`という形をしていたら`P → Q`と`Q → P`という二つのゴールに分解する -/
syntax (name := iffConstructor) "iff_constructor" : tactic

open Lean Elab Tactic Qq Meta

/-- ゴールが `P ↔ Q` の形をしているかチェックして、
`P ↔ Q` の形をしていたら `P` と `Q` をそれぞれ返す -/
def extractIffGoals : TacticM (Q(Prop) × Q(Prop)) := do
  have tgt : Q(Prop) := ← getMainTarget -- 右辺でQqを使用していないのでhaveを使う
  match tgt with
  | ~q($p ↔ $q) => return (p, q)
  | _ => throwError "ゴールが `P ↔ Q` の形ではありません。"

@[tactic iffConstructor]
def evalIffConstructor : Tactic := fun _stx => withMainContext do
  -- ゴールを取得する
  let goal ← getMainGoal
  have (p, q) := ← extractIffGoals

  -- 新しいメタ変数（ゴール）を作成する
  have mp : Q($p → $q) := ← mkFreshExprSyntheticOpaqueMVar q($p → $q) (tag := `mp)
  have mpr : Q($q → $p) := ← mkFreshExprSyntheticOpaqueMVar q($q → $p) (tag := `mpr)

  -- ゴールを`?_ ↔ ?_`の形にはめる
  goal.assign q(Iff.intro $mp $mpr)

  -- アクティブなゴールのリストは自動的には更新されないので、
  -- ２つのゴールを作ったことを宣言する
  replaceMainGoal [mp.mvarId!, mpr.mvarId!]

example : True ↔ True := by
  iff_constructor
  · simp
  · simp
