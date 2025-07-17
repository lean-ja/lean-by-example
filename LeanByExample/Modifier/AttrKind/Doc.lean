/-
> `attrKind` matches `("scoped" <|> "local")?`, used before an attribute like `@[local simp]`.
-/
--#--
import LeanByExample.DocCmd
/--
info: `attrKind` matches `("scoped" <|> "local")?`, used before an attribute like `@[local simp]`.
-/
#guard_msgs in
#doc Lean.Parser.Term.attrKind
--#--
