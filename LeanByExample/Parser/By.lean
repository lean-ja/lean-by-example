/- # by

Lean においては、命題は型で、証明はその項です。命題 `P` の証明を構成するとは項 `h : P` を構成するということです。`by` は、証明の構成をタクティクで行いたいときに使います。

証明項による証明とは、たとえば次のようなものです。 -/
import Lean --#

variable (P Q R : Prop)

-- `P → R` というのは `P` の証明を与えられたときに `R` の証明を返す関数の型
-- したがって、その証明は関数となる
example (hPQ : P → Q) (hQR : Q → R) : P → R :=
  fun hP ↦ hQR (hPQ hP)

/- 同じ命題をタクティクを使って示すと、例えば次のようになります。 -/

-- 同じ命題をタクティクで示した例
example (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  exact hQR (hPQ hP)

/- ## by?

`by` の代わりに `by?` を使うとタクティクモードで構成した証明を直接構成した証明に変換してくれます。詳細は [`show_term`](#{root}/Tactic/ShowTerm.md) のページを参照してください。
-/

/-⋆-//-- info: Try this: fun hP => hQR (hPQ hP) -/
#guard_msgs in --#
example (hPQ : P → Q) (hQR : Q → R) : P → R := by?
  intro hP
  exact hQR (hPQ hP)

/- ## 構文的な性質

タクティクを使用する際には多くの場合 `by` を伴うので、`by` とタクティクの関連は深いのですが、`by` 自身は構文的にタクティクではありません。
-/

open Lean Parser in

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

-- `by` 自身は構文的にタクティクではない
/-⋆-//-- error: <input>:1:0: expected tactic -/
#guard_msgs in --#
#eval parse `tactic "by"

/- `by` のパーサのドキュメントコメントに書かれている通り、`by` の後にタクティクを続けたものは項(term)になります。-/

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name ← liftCoreM do realizeGlobalConstNoOverload x
  if let some s ← findDocString? (← getEnv) name then
  logInfo m!"{s}"

/-⋆-//-- info: `by tac` constructs a term of the expected type by running the tactic(s) `tac`. -/
#guard_msgs in --#
#doc Lean.Parser.Term.byTactic

-- `by` の後にタクティクを続けたものは構文的に項(term)になる
#eval parse `term "by rfl"
