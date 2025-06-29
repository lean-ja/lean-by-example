/- # Tactic

`Lean.Elab.Tactic.Tactic` 型の項は、タクティクの内部実装を表現しています。タクティクとは証明の状態を操作する関数であり、`Tactic` 型は `Syntax → TacticM Unit` という関数型そのものです。
-/
import Lean
import Qq --#
import Batteries.Tactic.Exact --#

example : Lean.Elab.Tactic.Tactic = (Lean.Syntax → Lean.Elab.Tactic.TacticM Unit) := by rfl

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

/- ### And 専用 constructor

[`constructor`](#{root}/Tactic/Constructor.md) タクティクの機能を制限し、`And` 型のゴールを分割する機能だけを持つタクティクを構成する例を示します。[^and_constructor]
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

    -- ゴールを`?_ ∧ ?_`の形にはめる
    goal.assign q(And.intro $left $right)

    -- アクティブなゴールのリストは自動的には更新されないので、
    -- ２つのゴールを作ったことを宣言する
    replaceMainGoal [left.mvarId!, right.mvarId!]
end

example : True ∧ True := by
  and_constructor
  · trivial
  · trivial

/- ### Iff 専用 constructor

[`constructor`](#{root}/Tactic/Constructor.md) タクティクの機能を制限し、`P ↔ Q` という形のゴールを分解する機能だけを持つタクティクを構成する例を示します。[^iff_constructor]
-/

/-- ゴールが`P ↔ Q`という形をしていたら`P → Q`と`Q → P`という二つのゴールに分解する -/
syntax (name := iffConstructor) "iff_constructor" : tactic

section
  open Lean Elab Tactic Qq Meta

  /-- ゴールが `P ↔ Q` の形をしているかチェックして、
  `P ↔ Q` の形をしていたら `P` と `Q` をそれぞれ返す -/
  def extracetIffGoals : TacticM (Q(Prop) × Q(Prop)) := do
    have tgt : Q(Prop) := ← getMainTarget -- 右辺でQqを使用していないのでhaveを使う
    match tgt with
    | ~q($p ↔ $q) => return (p, q)
    | _ => throwError "ゴールが `P ↔ Q` の形ではありません。"

  @[tactic iffConstructor]
  def evalIffConstructor : Tactic := fun _stx => withMainContext do
    -- ゴールを取得する
    let goal ← getMainGoal
    have (p, q) := ← extracetIffGoals

    -- 新しいメタ変数（ゴール）を作成する
    have mp : Q($p → $q) := ← mkFreshExprSyntheticOpaqueMVar q($p → $q) (tag := `mp)
    have mpr : Q($q → $p) := ← mkFreshExprSyntheticOpaqueMVar q($q → $p) (tag := `mpr)

    -- ゴールを`?_ ↔ ?_`の形にはめる
    goal.assign q(Iff.intro $mp $mpr)

    -- アクティブなゴールのリストは自動的には更新されないので、
    -- ２つのゴールを作ったことを宣言する
    replaceMainGoal [mp.mvarId!, mpr.mvarId!]
end

example : True ↔ True := by
  iff_constructor
  · simp
  · simp

/- ### `A₁ ∧ A₂ ∧ ... ∧ Aₙ` という形の前提から `⊢ Aᵢ` を示すタクティク
`h : A₁ ∧ A₂ ∧ ... ∧ Aₙ` という形の前提から `⊢ Aᵢ` を示すタクティクを実装する例を示します。これは引数を持つタクティクの例であるとともに、再帰的な挙動をするタクティクの例でもあります。[^destruct_and]
-/

/-- `A₁ ∧ A₂ ∧ ... ∧ Aₙ` という形の前提から `⊢ Aᵢ` を示すタクティク -/
syntax (name := destructAnd) "destruct_and" ident : tactic

section
  open Lean Elab Tactic Qq Meta

  /-- 証明の前提 `hp : Expr` が `A₁ ∧ A₂ ∧ ... ∧ Aₙ` の形の命題の証明であるかチェックして、
  再帰的に分解して現在のゴールと一致する証明が得られるかを確認し、
  もし一致すればゴールを閉じて`true`を返す。一致しなければ`false`を返す。 -/
  partial def destructAndExpr (hp : Expr) : TacticM Bool := withMainContext do
    -- 今証明を構成しようとしている命題を取得
    have target : Q(Prop) := ← getMainTarget

    -- 前提として証明が得られている命題を取得
    have P : Q(Prop) := ← inferType hp
    have hp : Q($P) := hp -- 前提の型をQqで注釈

    -- `P` が `target` と一致しているなら、示すべきゴールの証明が得られたことになる。
    if (← isDefEq P target) then
      let goal ← getMainGoal
      goal.assignIfDefEq hp
      return true

    match P with
    | ~q($Q ∧ $R) =>
      let hq : Q($Q) := q(And.left $hp)
      let success ← destructAndExpr hq -- 再帰的にチェック
      -- 成功していたら早期リターン
      if success then
        return true

      let hr : Q($R) := q(And.right $hp)
      destructAndExpr hr -- 再帰的にチェック
    | _ => return false

  @[tactic destructAnd]
  def evalDestructAnd : Tactic := fun stx => withMainContext do
    match stx with
    | `(tactic| destruct_and $h) =>
      let h ← getFVarFromUserName h.getId
      let success ← destructAndExpr h
      if !success then
        failure

    | _ => throwUnsupportedSyntax
end

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

/- [^trivial]: このコード例を書くにあたり [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide) を参考にしました。

[^and_constructor]: このコード例を書くにあたり [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide) を参考にしました。

[^iff_constructor]: このコード例を書くにあたり [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/) を参考にしました。

[^destruct_and]: このコード例を書くにあたり The Hitchhiker's Guide to Logical Verification を参考にしました。
-/
