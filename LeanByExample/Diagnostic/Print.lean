/- # \#print
`#print` コマンドには複数の機能がありますが、単体で使うと定義を表示することができます。
-/
import Lean --#

/--
info: inductive Or : Prop → Prop → Prop
number of parameters: 2
constructors:
Or.inl : ∀ {a b : Prop}, a → a ∨ b
Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/
#guard_msgs in #print Or

/--
info: theorem Nat.add_succ : ∀ (n m : Nat), n + m.succ = (n + m).succ :=
fun n m => rfl
-/
#guard_msgs in #print Nat.add_succ

/--
info: structure And (a b : Prop) : Prop
number of parameters: 2
fields:
  And.left : a
  And.right : b
constructor:
  And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
-/
#guard_msgs in #print And

/- ## 利用可能な構文
`#print` 単体で利用できるほか、サブコマンドも定義されています。利用できるサブコマンドの全体は、エラーメッセージから確認できますが、以下の通りです。
* `axioms`
* `eqns`
* `equations`
* `tactic`
-/
open Lean Parser in

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

/--
error: <input>:1:7:
expected 'axioms', 'eqns', 'equations', 'tactic', identifier or string literal
-/
#guard_msgs in
  #eval parse `command "#print axiom"

/- また、このエラーメッセージから、`#print` コマンドに直接渡せるのは識別子(identifier)または文字列リテラル(string literal)だけであることが確認できます。識別子ではない一般の項(term)を渡すと、構文エラーになります。-/

open Lean in

/--
error: application type mismatch
  a.raw
argument
  a
has type
  TSyntax `term : Type
but is expected to have type
  TSyntax [`ident, `str] : Type
-/
#guard_msgs in run_meta
  let a ← `(1 + 1)
  let _ ← `(#print $a)

/-
## \#print axioms: 依存公理の確認
### 概要

`#print axioms` で、与えられた証明項が依存する公理を出します。たとえば Lean では排中律は選択原理 [`Classical.choice`](#{root}/Declarative/Axiom.md#ClassicalChoice) を使って証明するので、排中律は選択原理に依存しています。
-/

/-- 排中律 -/
example : ∀ (p : Prop), p ∨ ¬p := Classical.em

/-- info: 'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
  #print axioms Classical.em

/- また、`sorry` という命題を「証明したことにする」タクティクがありますが、これは `sorryAx` という万能な公理を導入していることが確認できます。-/

#guard_msgs (drop warning) in --#
theorem contra : False := by sorry

/-- info: 'contra' depends on axioms: [sorryAx] -/
#guard_msgs in
  #print axioms contra

/- ### 舞台裏
`Lean.collectAxioms` という関数を使用することにより、依存公理を調べて何かを行うような `#print axioms` の類似コマンドを自作することができます。ここでは例として、[`elab`](#{root}/Declarative/Elab.md) コマンドを使用して「ある定理が選択原理 `Classical.choice` に依存しているかどうか調べて、依存していればエラーにする」というコマンドを作成します。
-/
section
  open Lean Elab Command

  /-- 選択原理に依存していないことを検証するコマンド -/
  elab "#detect_classical " id:ident : command => do
    -- 識別子(ident)を Name に変換
    let constName ← liftCoreM <| realizeGlobalConstNoOverload id

    -- 依存する公理を取得
    let axioms ← collectAxioms constName

    -- 依存公理がなかったときの処理
    if axioms.isEmpty then
      logInfo m!"'{constName}' does not depend on any axioms"
      return ()

    -- Classical で始まる公理があるかどうかチェック
    -- もしあればエラーにする
    let caxes := axioms.filter fun nm => Name.isPrefixOf `Classical nm
    if caxes.isEmpty then
      logInfo m!"'{constName}' is non-classical and depends on axioms: {axioms.toList}"
    else
      throwError m!"'{constName}' depends on classical axioms: {caxes.toList}"
end

-- 以下はテストコード

/-- info: 'Nat.add_zero' does not depend on any axioms -/
#guard_msgs in
  #detect_classical Nat.add_zero

/-- info: 'Nat.div_add_mod' is non-classical and depends on axioms: [propext] -/
#guard_msgs in
  #detect_classical Nat.div_add_mod

/-- error: 'Classical.em' depends on classical axioms: [Classical.choice] -/
#guard_msgs in
  #detect_classical Classical.em
