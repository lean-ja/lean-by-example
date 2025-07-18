import Playground.PIH.Ch09.S06

/-- 証明に対する sorryAx -/
axiom sorryProofAx {P : Prop} : P

/-- 証明に対する sorry。実行不能になることを防ぎ、warning を出させない -/
macro "sorry_proof" : tactic => `(tactic| exact sorryProofAx)

/-- 評価に成功する式。

**Note** 評価に失敗する式を最初から除外することで高速化を狙いたい。-/
structure Result where
  /-- 式 -/
  expr : Expr
  /-- 式全体を評価した値 -/
  val : Pos
  /-- Result の仕様。`expr` を評価した値が `val` に一致する。 -/
  spec : expr.eval = some val := by sorry_proof

private def Result.toString (r : Result) : String :=
  s!"({r.expr}, {r.val})"

instance : ToString Result := ⟨Result.toString⟩

/-- 与えられた数がそれぞれ指定した回数ずつ使われている式をすべて返す -/
partial def Result.results (nums : List Pos) : List Result :=
  match nums with
  | [] => []
  | [num] => [⟨Expr.val num, num, by rfl⟩]
  | ns => do
    let (ls, rs) ← ns.split
    let l ← results ls
    let r ← results rs
    combine' l r
where
  /-- 結果を演算子で組み合わせる -/
  combine' (l r : Result) : List Result :=
    match l, r with
    | ⟨l, x, _⟩, ⟨r, y, _⟩ => do
      let op ← Op.asList
      if h : op.valid x y then
        -- 無名コンストラクタは、デフォルト値を受け付けることができない。
        return {expr := Expr.app op l r, val := op.vapply x y}
      else []

/-- info: [(1+2, 3)] -/
#guard_msgs in
  #eval Result.results [1, 2]

/-- 高速化した Expr.solutions 関数 -/
def Expr.fastSolutions (nums : List Pos) (target : Pos) : List Expr := do
  let nums' ← nums.choices
  let e ← Result.results nums'
  guard <| e.val == target
  return e.expr

theorem Expr.solution_impl : Expr.solutions = Expr.fastSolutions := by sorry_proof

-- `Expr.solutions` の代わりに高速な実装を使用する。
attribute [csimp] Expr.solution_impl
