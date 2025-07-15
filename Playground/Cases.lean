import Lean
import Qq
import Batteries

open Lean Elab Tactic Meta Qq Parser Term

set_option linter.unusedVariables false

/-- 命題`P`とその証明項`hp`を受け取り、`P = Q₁ ∧ Q₂ ∧ ... ∧ Qₙ` という形だった場合には
各`Qᵢ`とその証明項`hqᵢ`のリストを返す。その形でなければ単に`[(P, hp)]`を返す。-/
partial def destructAnd (P : Q(Prop)) (hp : Q($P)) : TacticM (List (Q(Prop) × Expr)) := do
  if (← inferType hp) != P then
    throwError "型の不一致エラー: {hp} は {P} の証明ではありません"

  if let ~q($Q₁ ∧ $Q₂) := P then
    let hq₁ : Q($Q₁) := q(And.left $hp)
    let hq₂ : Q($Q₂) := q(And.right $hp)
    return (← destructAnd Q₁ hq₁) ++ (← destructAnd Q₂ hq₂)
  else
    return [(P, hp)]

def casesAnd : TacticM Unit := withMainContext do
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

    let proofList ← destructAnd P hp
    for ((Q, hq), idx) in proofList.zipIdx do
      let hypName := decl.userName.appendAfter s!"_{idx}"
      trace[debug] m!"新しい仮定を追加: {Q}"
      evalTactic <| ← `(tactic| have $(mkIdent hypName) : $(← Q.toSyntax) := $(← hq.toSyntax))

/-- 仮定にある `A₁ ∧ A₂ ∧ ... ∧ Aₙ` を分解する -/
elab "cases_and" : tactic => casesAnd

set_option trace.debug true

example (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ d := by
  cases_and
  constructor <;> assumption
