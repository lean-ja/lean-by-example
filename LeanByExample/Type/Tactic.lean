/- # Tactic

`Lean.Elab.Tactic.Tactic` 型の項は、タクティクの内部実装を表現しています。タクティクとは証明の状態を操作する関数であり、`Tactic` 型は `Syntax → TacticM Unit` という関数型そのものです。
-/
import Lean
import Qq --#
import Batteries.Tactic.Exact --#

open Lean Elab Tactic in

example : Tactic = (Syntax → TacticM Unit) := by rfl

/- ## Tactic 型からタクティクを作る

`Tactic` 型の項からはタクティクを定義することができます。

### trivial タクティクの制限版

[`trivial`](#{root}/Tactic/Trivial.md) タクティクの機能を制限し、`True` というゴールを閉じる機能だけを持つタクティクを構成することができます。[^trivial]
-/

syntax (name := myTrivial) "my_trivial" : tactic

open Lean Elab Tactic Qq in

@[tactic myTrivial]
def evalMyTrivial : Tactic := fun _stx => do
  -- 現在のゴールを取得する
  let goal : MVarId ← getMainGoal
  try
    -- ゴールが `True.intro` で閉じられるか試す
    goal.assignIfDefEq q(True.intro)
  catch _error =>
    -- 失敗した場合はゴールの型を取得してエラーメッセージを表示する
    let goalType ← goal.getType
    throwError "my_trivialタクティクが失敗しました。ゴールの型は`{goalType}`であって`True`ではありません。"

example : True := by
  my_trivial

/-⋆-//-- error: my_trivialタクティクが失敗しました。ゴールの型は`False`であって`True`ではありません。 -/
#guard_msgs in --#
example : False := by
  my_trivial

/- ### assumption タクティク

[`assumption`](#{root}/Tactic/Assumption.md) タクティクのように、ゴールの証明が既に仮定にあるときにゴールを閉じるタクティクは次のように `Tactic` 型の関数によって実装できます。
-/

syntax (name := myAssumption) "my_assumption" : tactic

open Lean Elab Tactic in

@[tactic myAssumption]
def evalMyAssumption : Tactic := fun _stx => withMainContext do
  -- 現在のゴールとローカルコンテキストを取得する
  let goal ← getMainGoal
  let ctx ← getLCtx

  for (decl : LocalDecl) in ctx do
    -- ローカル宣言の種類がデフォルトでない場合はスキップする
    if decl.kind != .default then
      continue
    try
      -- ゴールにローカル宣言の変数を代入する
      goal.assignIfDefEq decl.toExpr
      -- 成功したら終了
      return
    catch _ =>
      -- 失敗しても無視して次の候補に進む
      pure ()
  throwError "my_assumptionタクティクが失敗しました。"

example {P : Prop} (hP : P) : P := by
  my_assumption

/-⋆-//-- error: my_assumptionタクティクが失敗しました。 -/
#guard_msgs in --#
example {P Q : Prop} (hP : P) : Q := by
  my_assumption

/- ### constructor タクティクの制限版

[`constructor`](#{root}/Tactic/Constructor.md) タクティクの機能を制限し、`And` 型のゴールを分割する機能だけを持つタクティクを構成する例を示します。[^constructor]
-/

/-- ゴールが`P ∧ Q`という形をしていたら、分解してそれぞれ別ゴールにする -/
syntax (name := andConstructor) "and_constructor" : tactic

section
  open Lean Elab Tactic Qq Meta

  /-- ゴールが `P ∧ Q` の形をしているかチェックして、
  `P ∧ Q` の形をしていたら `P` と `Q` をそれぞれ返す -/
  def extracetAndGoals : TacticM (Q(Prop) × Q(Prop)) := do
    have tgt : Q(Prop) := ← getMainTarget -- 右辺でQqを使用していないのでhaveを使う
    match tgt with
    | ~q($p ∧ $q) => return (p, q)
    | _ => throwError "ゴールが `P ∧ Q` の形ではありません。"

  -- テスト
  example : True ∧ True := by
    run_tac
      let (p, q) ← extracetAndGoals
      logInfo m!"ゴールは {p} ∧ {q} の形です。"

    constructor <;> trivial

  @[tactic andConstructor]
  def evalAndConstructor : Tactic := fun _stx => withMainContext do
    -- ゴールを取得する
    let goal ← getMainGoal
    have (p, q) := ← extracetAndGoals

    -- 新しいメタ変数（ゴール）を作成する
    have left : Q($p) := ← mkFreshExprSyntheticOpaqueMVar p (tag := `left)
    have right : Q($q) := ← mkFreshExprSyntheticOpaqueMVar q (tag := `right)

    -- ゴールを`?_ ∧ ?_`の形にする
    goal.assign q(And.intro $left $right)

    -- アクティブなゴールのリストは自動的には後進されないので、
    -- ２つのゴールを作ったことを宣言する
    replaceMainGoal [left.mvarId!, right.mvarId!]
end

example : True ∧ True := by
  and_constructor
  · trivial
  · trivial

/- [^trivial]: このコード例を書くにあたり [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide) を参考にしました。

[^constructor]: このコード例を書くにあたり [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide) を参考にしました。
-/
