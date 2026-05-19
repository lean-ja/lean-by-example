/- # \#print
`#print` コマンドには複数の機能がありますが、単体で使うと定義を表示することができます。
-/
import Lean --#
set_option warn.sorry false --#

/-⋆-//--
info: inductive Or : Prop → Prop → Prop
number of parameters: 2
constructors:
Or.inl : ∀ {a b : Prop}, a → a ∨ b
Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/
#guard_msgs in --#
#print Or

/-⋆-//--
info: @[defeq] theorem Nat.add_succ : ∀ (n m : Nat), n + m.succ = (n + m).succ :=
fun n m => rfl
-/
#guard_msgs in --#
#print Nat.add_succ

/-⋆-//--
info: structure And (a b : Prop) : Prop
number of parameters: 2
fields:
  And.left : a
  And.right : b
constructor:
  And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
-/
#guard_msgs in --#
#print And

/- ## 利用可能な構文
`#print` 単体で利用できるほか、サブコマンドも定義されています。利用できるサブコマンドの全体は、エラーメッセージから確認できますが、以下の通りです。
* `axioms`
* `eqns`
* `equations`
* `sig`
* `tactic`
-/
open Lean Parser in

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

/-⋆-//--
error: <input>:1:7: expected 'axioms', 'eqns', 'equations', 'sig', 'tactic', identifier or string literal
-/
#guard_msgs in --#
#eval parse `command "#print axiom"

/- また、このエラーメッセージから、`#print` コマンドに直接渡せるのは識別子(identifier)または文字列リテラル(string literal)だけであることが確認できます。識別子ではない一般の項(term)を渡すと、構文エラーになります。-/

open Lean in

/-⋆-//--
error: Application type mismatch: The argument
  a
has type
  TSyntax `term
but is expected to have type
  TSyntax [`ident, `str]
in the application
  a.raw
-/
#guard_msgs in --#
run_meta
  let a ← `(1 + 1)
  let _ ← `(#print $a)

/-
## \#print axioms: 依存公理の確認 { #PrintAxioms }
### 概要

`#print axioms` で、与えられた証明項が依存する公理を出します。たとえば Lean では排中律は選択原理 [`Classical.choice`](#{root}/Declarative/Axiom.md#ClassicalChoice) を使って証明するので、排中律は選択原理に依存しています。
-/

/-- 排中律 -/
example : ∀ (p : Prop), p ∨ ¬p := Classical.em

/-⋆-//-- info: 'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in --#
#print axioms Classical.em

/- また、`#print axioms` は不正な証明を見つけるのにも有用です。[`sorry`](#{root}/Tactic/Sorry.md) という命題を「証明したことにする」タクティクがありますが、これは `sorryAx` という万能な公理を導入していることが確認できます。-/

theorem contra : False := by sorry

/-⋆-//-- info: 'contra' depends on axioms: [sorryAx] -/
#guard_msgs in --#
#print axioms contra

/- ただし、`#print axioms` で常に不正な証明が発見できるわけではありません。たとえば [`debug.skipKernelTC`](#{root}/Option/SkipKernelTC.md) オプションを使用することですり抜けることができてしまいます。 -/

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

-- 依存公理がないケース
/-⋆-//-- info: 'Nat.add_zero' does not depend on any axioms -/
#guard_msgs in --#
#detect_classical Nat.add_zero

-- 選択公理に依存しないケース
/-⋆-//-- info: 'Nat.div_add_mod' is non-classical and depends on axioms: [propext] -/
#guard_msgs in --#
#detect_classical Nat.div_add_mod

-- 選択公理に依存するときはエラー
/-⋆-//-- error: 'Classical.em' depends on classical axioms: [Classical.choice] -/
#guard_msgs in --#
#detect_classical Classical.em

/-
## \#print opaque: opaque 定数と partial 関数の確認 { #PrintOpaque }

`#print axioms` に類似したカスタムコマンド `#print opaque` を実装することができます。
このコマンドは、与えられた定義が推移的に依存している [`opaque`](#{root}/Declarative/Opaque.md) 定数と [`partial`](#{root}/Modifier/Partial.md) 関数を列挙します。

これは **partial 遺伝**（ある定義が `partial` 関数に依存することで、その定義についても証明上の制約を引き継ぐこと）を発見するのに有用です。[`while`](#{root}/DoSyntax/While.md) 構文にも適用することができます。
-/
section
  open Lean Elab Command

  /-- ある定数が依存している `opaque` 定数と `partial` 関数を収集する -/
  private def collectOpaqueConsts (constName : Name) : CommandElabM (Array Name) := do
    let env ← getEnv
    let mut visited : NameSet := {}
    let mut result  : NameSet := {}
    let mut queue   : Array Name := #[constName]
    while !queue.isEmpty do
      let name := queue.back!
      queue := queue.pop
      if !visited.contains name then
        visited := visited.insert name
        match env.find? name with
        | some (.opaqueInfo v) =>
          result := result.insert name
          for dep in v.type.getUsedConstants do
            if !visited.contains dep then
              queue := queue.push dep
          for dep in v.value.getUsedConstants do
            if !visited.contains dep then
              queue := queue.push dep
        | some (.defnInfo v) =>
          if let .partial := v.safety then
            result := result.insert name
          for dep in v.value.getUsedConstants do
            if !visited.contains dep then
              queue := queue.push dep
          for dep in v.type.getUsedConstants do
            if !visited.contains dep then
              queue := queue.push dep
        | some (.axiomInfo v) =>
          for dep in v.type.getUsedConstants do
            if !visited.contains dep then
              queue := queue.push dep
        | _ => pure ()
    return result.toArray.qsort Name.lt

  /-- `#print opaque` コマンド: 依存している `opaque` 定数と `partial` 関数を表示する -/
  elab "#print" "opaque" id:ident : command => do
    let constName ← liftCoreM <| realizeGlobalConstNoOverload id
    let opaques ← collectOpaqueConsts constName
    if opaques.isEmpty then
      logInfo m!"'{constName}' does not depend on any opaque or partial constants"
    else
      logInfo m!"'{constName}' depends on opaque/partial: {opaques.map MessageData.ofConstName |>.toList}"

end

-- `opaque` で宣言した定数が検出される
opaque exPrintOpaque : Nat

/-⋆-//-- info: 'exPrintOpaque' depends on opaque/partial: [exPrintOpaque] -/
#guard_msgs in --#
#print opaque exPrintOpaque

-- `partial def` が検出される
partial def exPrintOpaqueLoop (n : Nat) : Nat :=
  if n == 0 then 0 else exPrintOpaqueLoop (n - 1)

/-⋆-//-- info: 'exPrintOpaqueLoop' depends on opaque/partial: [exPrintOpaqueLoop] -/
#guard_msgs in --#
#print opaque exPrintOpaqueLoop

/- `partial` 関数を使って定義した関数に `partial` をつけなくても、依存関係から `partial` な定数が検出できる。これが **partial 遺伝** の発見に役立つ。 -/

-- partial 関数を使って定義した通常の def
def exPrintOpaqueUsing := @exPrintOpaqueLoop

/-⋆-//-- info: 'exPrintOpaqueUsing' depends on opaque/partial: [exPrintOpaqueLoop] -/
#guard_msgs in --#
#print opaque exPrintOpaqueUsing

/- `while` 構文を使った関数は、内部で `partial` 関数を使っているため、その依存関係も検出される。 -/

-- while を使った関数
def exPrintOpaqueWhile : Nat := Id.run do
  let mut n := 0
  while n < 10 do
    n := n + 1
  return n

-- while を使った関数は Lean.Loop.forIn という partial 関数に依存している
#print opaque exPrintOpaqueWhile
