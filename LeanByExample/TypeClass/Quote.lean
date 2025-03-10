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

### 候補を順に試すタクティク

`Quote` と [`elab`](#{root}/Declarative/Elab.md) コマンドを組み合わせると、たとえば「存在命題を、候補を順に試すことで示すタクティク」を自作することができます。
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

/- ### 論理式のための構文を用意する

次のように、Lean のデータとして論理式の AST を定義したとします。
-/

/-- 論理式 -/
inductive PropForm where
  /-- 真 `⊤` -/
  | tr : PropForm
  /-- 偽 `⊥` -/
  | fls : PropForm
  /-- 命題変数 -/
  | var : String → PropForm
  /-- 論理積 `∧` -/
  | conj : PropForm → PropForm → PropForm
  /-- 論理和 `∨` -/
  | disj : PropForm → PropForm → PropForm
  /-- 含意 `→` -/
  | impl : PropForm → PropForm → PropForm
  /-- 否定 `¬` -/
  | neg : PropForm → PropForm
  /-- 同値 `↔` -/
  | biImpl : PropForm → PropForm → PropForm
deriving Repr, DecidableEq, Inhabited

/- このとき、[`macro_rules`](#{root}/Declarative/MacroRules.md) コマンドと `Quote` を組み合わせることで、論理式のための構文を定義することができます。[^lamr] -/

declare_syntax_cat propform

/-- `PropForm` を見やすく定義するための構文 -/
syntax "prop!{" propform "}" : term

syntax:max ident : propform
syntax "⊤" : propform
syntax "⊥" : propform
syntax:35 propform:36 " ∧ " propform:35 : propform
syntax:30 propform:31 " ∨ " propform:30 : propform
syntax:20 propform:21 " → " propform:20 : propform
syntax:20 propform:21 " ↔ " propform:20 : propform
syntax:max "¬ " propform:40 : propform
syntax:max "(" propform ")" : propform

macro_rules
  | `(prop!{$p:ident}) => `(PropForm.var $(Lean.quote p.getId.toString))
  | `(prop!{⊤}) => `(ProfForm.tr)
  | `(prop!{⊥}) => `(ProfForm.fls)
  | `(prop!{¬ $p}) => `(PropForm.neg prop!{$p})
  | `(prop!{$p ∧ $q}) => `(PropForm.conj prop!{$p} prop!{$q})
  | `(prop!{$p ∨ $q}) => `(PropForm.disj prop!{$p} prop!{$q})
  | `(prop!{$p → $q}) => `(PropForm.impl prop!{$p} prop!{$q})
  | `(prop!{$p ↔ $q}) => `(PropForm.biImpl prop!{$p} prop!{$q})
  | `(prop!{($p:propform)}) => `(prop!{$p})

-- 構文が使用できるようになった
#check prop!{p ∧ q → (r ∨ ¬ p) → q}
#check prop!{p ∧ q ∧ r → p}

-- 構文のテスト
#guard
  let actual := prop!{p ∧ q}
  let expected := PropForm.conj (PropForm.var "p") (PropForm.var "q")
  expected == actual

/- [^lamr]: この例は [Logic and Mechanized Reasoning](https://github.com/avigad/lamr) を参考にしました。 -/
