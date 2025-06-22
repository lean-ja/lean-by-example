/- # Expr

`Lean.Expr` は Lean の **抽象構文木(abstract syntax tree)** を表すデータ型です。

具象構文木である [`Syntax`](#{root}/Type/Syntax.md) から `Expr` を得る操作のことを **エラボレート(elaborate)** と呼び、それを行う関数のことを **エラボレータ(elaborator)** と呼びます。

## Syntax と Expr の違い

具象構文木である [`Syntax`](#{root}/Type/Syntax.md) との違いを理解するために、具体的な例で比較してみましょう。
-/
import Lean
import Qq

open Qq in

/-- 排中律という命題に対応する `Expr` -/
def excludeMiddleExpr : Q(Prop) := q(∀ p : Prop, p ∨ ¬ p)


/-⋆-//-- info: "forall (p : Prop), Or p (Not p)" -/
#guard_msgs in --#
#eval toString excludeMiddleExpr

open Lean Parser

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

/-⋆-//--
info: (Term.forall "∀" [`p] [(Term.typeSpec ":" (Term.prop "Prop"))] "," («term_∨_» `p "∨" («term¬_» "¬" `p)))
-/
#guard_msgs in --#
#eval show MetaM Unit from do
  let stx ← parse `term "∀ p : Prop, p ∨ ¬ p"
  IO.println stx

/- [`Repr`](#{root}/TypeClass/Repr.md) の出力を比較すると極めて長くなるので [`ToString`](#{root}/TypeClass/ToString.md) の出力を比較しましたが、このように [`Syntax`](#{root}/Type/Syntax.md) の方には抽象度の低いコードの情報が含まれています。 -/
