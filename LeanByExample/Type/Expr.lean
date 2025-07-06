/- # Expr

`Lean.Expr` は Lean の **抽象構文木(abstract syntax tree)** を表すデータ型です。

具象構文木である [`Syntax`](#{root}/Type/Syntax.md) から `Expr` を得る操作のことを **エラボレート(elaborate)** と呼び、それを行う関数のことを **エラボレータ(elaborator)** と呼びます。

## Syntax と Expr の違い

具象構文木である [`Syntax`](#{root}/Type/Syntax.md) との違いを理解するために、具体的な例で比較してみましょう。
-/
import Lean
import Qq

section --#

open Qq Lean Parser

/-- コンストラクタを使って定義した `[1]` というリスト -/
def listByCtorExpr : Q(List Nat) := q(List.cons 1 List.nil)

/-⋆-//-- info: "List.cons.{0} Nat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (List.nil.{0} Nat)" -/
#guard_msgs in --#
#eval toString listByCtorExpr

/-- リストリテラルから定義した `[1]` というリスト -/
def listByListLitExpr : Q(List Nat) := q([1])

/-⋆-//-- info: "List.cons.{0} Nat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (List.nil.{0} Nat)" -/
#guard_msgs in --#
#eval toString listByListLitExpr


set_option hygiene false in

/-⋆-//-- info: "(Term.app `List.cons [(num \"1\") `List.nil])" -/
#guard_msgs in --#
#eval show MetaM String from do
  -- コンストラクタを使って定義した `[1]` というリストの Syntax
  let stx ← `(term| List.cons 1 List.nil)
  return toString stx

/-⋆-//-- info: "(«term[_]» \"[\" [(num \"1\")] \"]\")" -/
#guard_msgs in --#
#eval show MetaM String from do
  -- リストリテラルから定義した `[1]` というリストの Syntax
  let stx ← `(term| [1])
  return toString stx

end --#
/- [`Repr`](#{root}/TypeClass/Repr.md) の出力を比較すると極めて長くなるので [`ToString`](#{root}/TypeClass/ToString.md) の出力を比較しましたが、このように [`Syntax`](#{root}/Type/Syntax.md) は「同じものを意味するが構文が異なるもの」を区別する一方で、`Expr` は区別しません。
-/

/- ## 定義

`Expr` は Lean のソースコードの中で次のように定義されています。
-/
namespace Hidden --#

open Lean
--#--
-- # Expr の定義が変化していないことを確認するためのコード
/--
info: inductive Lean.Expr : Type
number of parameters: 0
constructors:
Lean.Expr.bvar : Nat → Expr
Lean.Expr.fvar : FVarId → Expr
Lean.Expr.mvar : MVarId → Expr
Lean.Expr.sort : Level → Expr
Lean.Expr.const : Name → List Level → Expr
Lean.Expr.app : Expr → Expr → Expr
Lean.Expr.lam : Name → Expr → Expr → BinderInfo → Expr
Lean.Expr.forallE : Name → Expr → Expr → BinderInfo → Expr
Lean.Expr.letE : Name → Expr → Expr → Expr → Bool → Expr
Lean.Expr.lit : Literal → Expr
Lean.Expr.mdata : MData → Expr → Expr
Lean.Expr.proj : Name → Nat → Expr → Expr
-/
#guard_msgs in #print Expr
--#--

inductive Expr where
  /-- 束縛変数 -/
  | bvar (deBruijnIndex : Nat)

  /-- 自由変数 -/
  | fvar (fvarId : FVarId)

  /-- メタ変数 -/
  | mvar (mvarId : MVarId)

  /-- 型の宇宙レベルを表す。 -/
  | sort (u : Level)

  /--
  （宇宙多相的な）定数であり、モジュール内で以前に定義されたか、
  import されたモジュールによって定義されたもの。
  -/
  | const (declName : Name) (us : List Level)

  /-- 関数適用 -/
  | app (fn : Expr) (arg : Expr)

  /-- ラムダ抽象(無名関数) -/
  | lam (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo)

  /-- 依存関数型 `(a : α) → β` -/
  | forallE (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo)

  /-- let 式 -/
  | letE (declName : Name) (type : Expr) (value : Expr) (body : Expr) (nonDep : Bool)

  /-- 自然数リテラルと文字列リテラル。 -/
  | lit : Literal → Expr

  /-- メタデータ（注釈） -/
  | mdata (data : MData) (expr : Expr)

  /-- 射影式(projection expression) -/
  | proj (typeName : Name) (idx : Nat) (struct : Expr)

end Hidden --#
/- ### bvar: 束縛変数

`Expr.bvar` は **束縛変数(bound variable)** を表します。つまり、式の中で `let` や `fun` や `∀` などで束縛された変数のことです。`deBrujinIndex` パラメータは **ド・ブラウンインデックス** を表します。

たとえば、具体的な式では次のようになります。
-/

open Qq in

/-⋆-//--
info: Lean.Expr.forallE `x (Lean.Expr.const `Nat [])
  ((((Lean.Expr.const `Eq [Lean.Level.zero.succ]).app (Lean.Expr.const `Nat [])).app (Lean.Expr.bvar 0)).app
    (Lean.Expr.bvar 0))
  Lean.BinderInfo.default
-/
#guard_msgs in --#
#eval q(∀ x : Nat, x = x)

/- ### fvar: 自由変数

`Expr.fvar` は **自由変数(free variable)** を表します。つまり、式の中で束縛されていない変数のことです。`fvarId` パラメータは自由変数の識別子です。

たとえば、証明において各時点で得られている仮定は自由変数であり `Expr.fvar` で表されます。
-/

open Lean Elab Tactic in

/-- 現在の証明の状態を表示するタクティク -/
elab "my_trace_state" : tactic => do
  -- 現在のローカルコンテキストを取得する
  let ctx ← getLCtx

  for (decl : LocalDecl) in ctx do
    let fvar := Expr.fvar decl.fvarId
    let type := decl.type
    logInfo m!"{fvar} : {type}"

/-⋆-//--
info: _example : ∀ (n : Nat), n > 5 → ∃ n, n > 5
---
info: n : Nat
---
info: hn : n > 5
-/
#guard_msgs in --#
example (n : Nat) (hn : n > 5) : ∃ n, n > 5 := by
  my_trace_state
  exists n

/- ### mvar: メタ変数

`Expr.mvar` はメタ変数を表します。メタ変数は、式におけるプレースホルダや穴だと考えることができます。つまり、後で具体的な値で埋めることが期待される変数です。

メタ変数の典型的な例は、証明における「現時点で示すべきゴール」です。
-/

open Lean Elab Tactic in

elab "show_goal" : tactic => do
  -- 現在のゴールを取得する
  let goal ← getMainGoal
  let goalExpr := Expr.mvar goal
  -- ゴールの式を表示する
  logInfo m!"{goalExpr}: {goal}"

set_option pp.mvars false in

/-⋆-//-- info: ?_: ⊢ True -/
#guard_msgs in --#
example : True := by
  show_goal
  trivial

/- ### sort: 宇宙レベル

`Expr.sort` は型の宇宙レベルを表します。
-/
section --#

universe u

open Lean Expr Qq

/-⋆-//-- info: sort Level.zero -/
#guard_msgs in --#
#eval q(Prop)

/-⋆-//-- info: sort Level.zero -/
#guard_msgs in --#
#eval q(Sort 0)

/-⋆-//-- info: sort Level.zero.succ -/
#guard_msgs in --#
#eval q(Type 0)

end --#
/- ### const: 定数

`Expr.const` は定数や関数を表します。
-/
section --#

open Lean Qq Expr

/-⋆-//-- info: const `Nat [] -/
#guard_msgs in --#
#eval q(Nat)

/-⋆-//-- info: const `Nat.zero [] -/
#guard_msgs in --#
#eval q(Nat.zero)

/-⋆-//-- info: const `Nat.succ [] -/
#guard_msgs in --#
#eval q(Nat.succ)

/-⋆-//-- info: const `List.map [Level.zero, Level.zero] -/
#guard_msgs in --#
#eval q(@List.map.{0, 0})

end --#
/- ### app: 関数適用

`Expr.app` は関数適用を表します。たとえば `f` と `e` に対応する `Expr` がそれぞれ `⟦f⟧` と `⟦e⟧` であるとき、`f e` に対応する `Expr` の項は `Expr.app ⟦f⟧ ⟦e⟧` です。
-/
section --#

open Lean Expr Qq

/-⋆-//-- info: (const `Nat.succ []).app (const `Nat.zero []) -/
#guard_msgs in --#
#eval q(Nat.succ Nat.zero)

end --#
/- ### lam: ラムダ抽象

`Expr.lam` はラムダ抽象を表します。つまり、無名関数を表します。-/
section --#

open Lean Expr Qq

/-⋆-//-- info: lam `x (const `Nat []) (bvar 0) BinderInfo.default -/
#guard_msgs in --#
#eval q(fun (x : Nat) => x)

end --#
/- 引数について説明しておきます。
* `binderName` は束縛変数の名前を表します。下の例では `x` です。
* `binderType` は束縛変数の型を表します。下の例では `Nat` です。
* `body` は関数の返り値を表します。下の例では `Expr.bvar 0` で、これは束縛変数 `x` を参照しています。
* `binderInfo` は束縛変数の情報を表します。明示的な引数なのか、暗黙の引数なのかといった情報を持ちます。
-/
section --#

open Lean Expr Qq Level

/-⋆-//-- info: "fun (x : Nat) => x" -/
#guard_msgs in --#
#eval show String from
  let expr := Expr.lam
    (binderName := `x)
    (binderType := q(Nat))
    (body := Expr.bvar 0)
    (binderInfo := .default)
  toString expr

/-⋆-//--
info: lam `α (sort zero.succ)
  (lam `x (bvar 0) ((((const `Eq [zero.succ]).app (bvar 1)).app (bvar 0)).app (bvar 0)) BinderInfo.default)
  BinderInfo.implicit
-/
#guard_msgs in --#
#eval q(fun {α : Type} (x : α) => x = x)

end --#
/- ### forallE: 依存関数型

`Expr.forallE` は依存関数型または全称量化を表現します。
-/
section --#

open Lean Expr Qq Level

/-⋆-//--
info: forallE `P (sort zero) (forallE Name.anonymous (bvar 0) (bvar 1) BinderInfo.default) BinderInfo.default
-/
#guard_msgs in --#
#eval q(∀ (P : Prop), P → P)

/-⋆-//--
info: forallE `n (const `Nat []) (((const `Vector [zero]).app (const `Nat [])).app (bvar 0)) BinderInfo.default
-/
#guard_msgs in --#
#eval q((n : Nat) → Vector Nat n)

end --#
/- ### letE: let 式

`Expr.letE` は let 式を表します。let 式は、変数を束縛してその値を後続の式で使用するために使われます。
-/
section --#

open Lean Expr Qq

/-⋆-//--
info: letE `x (const `Nat [])
  ((((const `OfNat.ofNat [Level.zero]).app (const `Nat [])).app (lit (Literal.natVal 0))).app
    ((const `instOfNatNat []).app (lit (Literal.natVal 0))))
  (bvar 0) false
-/
#guard_msgs in --#
#eval q(let x : Nat := 0; x)

end --#
/- ### lit: 自然数リテラルと文字列リテラル

`Expr.lit` は自然数リテラルや文字列リテラルを表します。
-/
section --#

open Lean Expr Qq

/-⋆-//-- info: lit (Literal.strVal "Lean is nice!") -/
#guard_msgs in --#
#eval q("Lean is nice!")

end --#
