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

/-
## \#print axioms: 依存公理の確認
### 概要

`#print axioms` で、与えられた証明項が依存する公理を出します。たとえば Lean では排中律は選択原理 [`Classical.choice`](../Declarative/Axiom.md#ClassicalChoice) を使って証明するので、排中律は選択原理に依存しています。
-/

/-- 排中律 -/
example : ∀ (p : Prop), p ∨ ¬p := Classical.em

/-- info: 'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
  #print axioms Classical.em

/- また、`sorry` という命題を「証明したことにする」タクティクがありますが、これは `sorryAx` という万能な公理を導入していることが確認できます。-/

theorem contra : False := by sorry

/-- info: 'contra' depends on axioms: [sorryAx] -/
#guard_msgs in
  #print axioms contra

/- ### 舞台裏
`#print axioms` コマンドは、内部で `Lean.collectAxioms` という関数を使用して公理を取得しています。これを利用すると、依存公理を調べて何かを行うコマンドを自作することができます。ここでは例として、「ある定理が選択原理 `Classical.choice` に依存しているかどうか調べて、依存していればエラーにする」というコマンドを作成します。
-/
section --#

open Lean Elab Command

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

end --#
/- ## よくあるエラー
`#print` コマンドは式ではなく名前を受け付けます。たとえば、`#print Nat.zero` はエラーになりませんが、`#print Nat.succ Nat.zero` はエラーになります。この挙動は `#eval` コマンドや `#check` コマンドとは異なるため、注意が必要です。
-/
section error --#

open Lean

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
#guard_msgs(error) in
  #eval! show Lean.Elab.Term.TermElabM Unit from do
    let a ← `(Nat.succ Nat.zero)
    let _b ← `(#print $a)

/- 上のコード例は、これを検証するものです。エラーメッセージにあるように `#print` は `ident` または `str` を期待しており、これはそれぞれ単一の識別子と文字列リテラルを意味します。`Nat.succ Nat.zero` は `term` つまり項なのでエラーになります。

`#check` や `#eval` の場合は項を受け付けるので、エラーになりません。-/

#eval show Lean.Elab.Term.TermElabM Unit from do
  let a ← `(Nat.succ Nat.zero)
  let _b ← `(#eval $a)

#eval show Lean.Elab.Term.TermElabM Unit from do
  let a ← `(Nat.succ Nat.zero)
  let _b ← `(#check $a)

end error --#
