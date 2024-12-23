/- # inherit_doc
`[inherit_doc]` 属性を指定すると、既存の定数などのドキュメントコメントを使いまわすことができます。
-/
import Lean

/-- 最初に与えた doc コメント -/
def greet := "hello"

-- `greet` のドキュメントコメントを引き継ぐ
@[inherit_doc greet] abbrev greet' := greet

section

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name ← liftCoreM do realizeGlobalConstNoOverload x
  if let some s ← findDocString? (← getEnv) name then
  logInfo m!"{s}"

end

/-- info: 最初に与えた doc コメント -/
#guard_msgs in #doc greet'

/- `[inherit_doc]` 属性を使用するのは、記法を導入する際であることが多いでしょう。この場合、ドキュメントコメントの継承元を指定する必要がありません。 -/

/-- `⊔` という記号のための型クラス -/
class Sup (α : Type) where
  /-- 最小上界、上限 -/
  sup : α → α → α

@[inherit_doc] infixl:68 " ⊔ " => Sup.sup
