/- # Tactic

`Lean.Elab.Tactic.Tactic` 型の項は、タクティクの内部実装を表現しています。タクティクとは証明の状態を操作する関数であり、`Tactic` 型は `Syntax → TacticM Unit` という関数型そのものです。
-/
import Lean
import Qq --#
import Batteries --#

example : Lean.Elab.Tactic.Tactic = (Lean.Syntax → Lean.Elab.Tactic.TacticM Unit) := by rfl

/- ## Tactic 型からタクティクを作る

`Tactic` 型の項からはタクティクを定義することができます。-/
/- ### tada で証明終了をお祝いするタクティク

[`done`](#{root}/Tactic/Done.md) タクティクの派生として、ゴールがなくなったら 🎉 でお祝いするタクティクを作ることができます。
-/
syntax (name := tada) "tada" : tactic

open Lean Elab Tactic Term in

@[tactic tada]
def evalTada : Tactic := fun _stx => do
  -- 現在の未解決のゴールを取得する
  let goals ← getUnsolvedGoals

  -- 未解決のゴールがある場合
  unless goals.isEmpty do
    reportUnsolvedGoals goals
    throwAbortCommand

  logInfo "🎉 おめでとうございます！証明完了です！"

/-⋆-//-- info: 🎉 おめでとうございます！証明完了です！ -/
#guard_msgs in --#
example : True := by
  trivial
  tada

/- ### trivial タクティクの制限版

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
section --#

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

end --#
/- ### Iff 専用 constructor

[`constructor`](#{root}/Tactic/Constructor.md) タクティクの機能を制限し、`P ↔ Q` という形のゴールを分解する機能だけを持つタクティクを構成する例を示します。[^iff_constructor]
-/
section --#

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

end --#
/- ### `A₁ ∧ A₂ ∧ ... ∧ Aₙ` という形の前提から `⊢ Aᵢ` を示すタクティク
`h : A₁ ∧ A₂ ∧ ... ∧ Aₙ` という形の前提から `⊢ Aᵢ` を示すタクティクを実装する例を示します。これは引数を持つタクティクの例であるとともに、再帰的な挙動をするタクティクの例でもあります。[^destruct_and]
-/
section --#

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

end --#
/- ### `A₁ ∧ ⋯ ∧ Aₙ` という形の前提を分解して新しい仮定として追加するタクティク

再帰的な挙動をするタクティクの例として、さらに `A₁ ∧ A₂ ∧ ... ∧ Aₙ` という形の前提を分解して新しい仮定として追加するタクティクを実装する例を示します。[^cases_and]
-/
section --#

/-- 仮定にある `A₁ ∧ A₂ ∧ ... ∧ Aₙ` を分解する -/
syntax (name := casesAnd) "cases_and" : tactic

open Lean Elab Tactic Meta Qq Parser Term

/-- 命題`P`とその証明項`hp`を受け取り、`P = Q₁ ∧ Q₂ ∧ ... ∧ Qₙ` という形だった場合には
各`Qᵢ`とその証明項`hqᵢ`のリストを返す。その形でなければ単に`[(P, hp)]`を返す。-/
partial def casesAndAux (P : Q(Prop)) (hp : Q($P)) : TacticM (List ((P : Q(Prop)) × Q($P))) := do
  if (← inferType hp) != P then
    throwError "型の不一致エラー: {hp} は {P} の証明ではありません"

  if let ~q($Q₁ ∧ $Q₂) := P then
    let hq₁ : Q($Q₁) := q(And.left $hp)
    let hq₂ : Q($Q₂) := q(And.right $hp)
    return (← casesAndAux Q₁ hq₁) ++ (← casesAndAux Q₂ hq₂)
  else
    return [⟨P, hp⟩]

@[tactic casesAnd]
def evalCasesAnd : Tactic := fun _stx => withMainContext do
  -- 現在のローカルコンテキストを取得する
  let ctx ← getLCtx

  for (decl : LocalDecl) in ctx do
    -- ローカル宣言の種類がデフォルトでない場合はスキップする
    if decl.kind != .default then
      continue

    -- `hp : P` (ただし `P : Prop`)というタイプのローカル宣言に絞り込む
    -- `A : Prop` のようなローカル宣言は除外する
    let declType := decl.type
    let declTypeType ← inferType declType
    if ! declTypeType.isProp then
      continue

    -- 宣言し直す
    have P : Q(Prop) := declType
    have hp : Q($P) := decl.toExpr
    trace[debug] m!"対象となるローカル宣言を見つけました: {hp} : {P}"

    let proofList ← casesAndAux P hp
    for (⟨Q, hq⟩, idx) in proofList.zipIdx do
      let hypName := decl.userName.appendAfter s!"_{idx}"
      trace[debug] m!"新しい仮定を追加: {Q}"
      evalTactic <| ← `(tactic| have $(mkIdent hypName) : $(← Q.toSyntax) := $(← hq.toSyntax))

-- デバッグ出力をOFFにする
set_option trace.debug false

/-⋆-//--
trace: a b c d : Prop
h : a ∧ (b ∧ c) ∧ d
h_0 : a
h_1 : b
h_2 : c
h_3 : d
⊢ b ∧ d
-/
#guard_msgs in --#
example (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ d := by
  cases_and
  trace_state -- 現在の infoview の状態を表示

  constructor <;> assumption

end --#
/- ### exact? タクティク

ゴールを直接閉じることができる定理を探すタクティクとして [`exact?`](#{root}/Tactic/ExactQuestion.md) タクティクがあります。これに相当する（しかしかなり原始的で低性能な）ものを自前で実装する例を示します。[^exact?]
-/

-- `my_exact?` というタクティックの構文を定義する（構文として `my_exact?` を認識させる）
syntax (name := myExact?) "my_exact?" : tactic

open Lean Elab Tactic in

-- `my_exact?` タクティックの実装を定義する
@[tactic myExact?]
def evalMyExact? : Tactic := fun _stx => do
  -- 現在の環境（定理などが格納されている）を取得
  let env ← getEnv

  -- 環境中の定数を取得し、以下の条件でフィルターする：
  -- 1. unsafe な定数ではない
  -- 2. 種類が axiom か thm（定理）のもの
  let theorems : List Name := SMap.toList (Environment.constants env)
    |>.filter (fun (_name, info) => ! ConstantInfo.isUnsafe info)
    |>.filterMap (fun (name, _info) => do
        let kind ← getOriginalConstKind? env name
        match kind with
        | .axiom | .thm => name
        | _ => none
      )

  -- 条件を満たす定理に対して順に試す
  for name in theorems do
    try
      -- 名前を構文ノードに変換
      let nameStx := mkIdent name

      -- `apply name <;> assumption` を構文的に展開・実行する
      evalTactic <| ← `(tactic| apply $nameStx <;> assumption)

      -- 成功したらログを出力し、タクティックの実行を終了する
      logInfo m!"Applied {name} successfully."
      return

    catch _ =>
      -- 失敗しても続行（次の定理を試す）
      continue

  -- どの定理も適用できなかった場合はタクティックとして失敗を返す
  failure

set_option maxHeartbeats 500000 in

-- 使用例
example (x y : Nat) (h : x = y) : y = x := by
  my_exact?

/- [^trivial]: このコード例を書くにあたり [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide) を参考にしました。

[^and_constructor]: このコード例を書くにあたり [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide) を参考にしました。

[^iff_constructor]: このコード例を書くにあたり [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/) を参考にしました。

[^destruct_and]: このコード例を書くにあたり [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025) を参考にしました。

[^exact?]: このコード例を書くにあたり [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025) を参考にしました。

[^cases_and]: このコード例を書くにあたり [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025) の演習問題を参考にしました。
-/
