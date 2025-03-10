import Lean --#
/- # Quote

`Lean.Quote` は、構文の **クォート(quote)** を行います。つまり、データ `x : α` を対応する [構文木](#{root}/Type/Syntax.md) に変換します。構文木への変換という点ではパースに似ていますが、パースはいろんな型からの変換ではなく、コードの文字列からの変換です。
-/

open Lean

/-⋆-//-- info: (num "1") -/
#guard_msgs in --#
#eval
  let x : TSyntax `term := Quote.quote 1
  IO.println x

/-⋆-//-- info: `Bool.true._@._internal._hyg.0 -/
#guard_msgs in --#
#eval
  let x : TSyntax `term := Quote.quote true
  IO.println x
/- なお [export](#{root}/Declarative/Export.md) されているので、`Lean.Quote.quote` の代わりに単に `Lean.quote` と書くことができます。 -/
section
  variable {α : Type} [Lean.Quote α `term]

  example (x : α) : (Lean.Quote.quote x : Lean.TSyntax `term) = Lean.quote x := by
    rfl
end

/- ## 使用例

これを使うと、たとえば「存在命題を、候補を順に試すことで示すタクティク」を自作することができます。
-/

open Lean Elab.Tactic Elab.Term in

elab "try_for" n:num : tactic => do
  -- 範囲として与えられた自然数を取得
  let n := n.getNat

  -- `n` までの数を順に試す
  for i in [0 : n+1] do
    let istx := quote i

    -- `evalTactic` を使ってタクティクを呼び出して実行する
    evalTactic <| ← `(tactic| try { exists $istx })

example : ∃ n : Nat, n * 24 = 48 := by
  -- 具体的な数を指定しなくても探す範囲を指定するだけで示すことができる
  try_for 10

example : ∃ n : Nat, (n + 2) / 3 = 5 := by
  -- 12 まで試しても見つからない
  fail_if_success solve
  | try_for 12

  -- 13 まで試すと見つかる
  try_for 13
