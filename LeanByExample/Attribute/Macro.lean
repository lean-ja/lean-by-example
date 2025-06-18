/- # macro

`[macro]` 属性は、[`Macro`](#{root}/Type/Macro.md) 型を持つ項をマクロとして動作するようにします。
-/
import Lean

open Lean

syntax:10 (name := lxor) term:10 " LXOR " term:11 : term

def lxorImpl : Macro := fun stx =>
  match stx with
  | `($l:term LXOR $r:term) => `(term| !$l && $r)
  | _ => Macro.throwUnsupported

-- 解釈不能というエラーになる
#check_failure true LXOR false

-- マクロとして登録する
attribute [macro lxor] lxorImpl

-- マクロ展開されるので、`!true && false` になる
#guard (true LXOR false) = false

/- `[macro]` 属性は低レベルな機能です。多くの用途では [`macro_rules`](#{root}/Declarative/MacroRules.md) コマンドや [`macro`](#{root}/Declarative/Macro.md) コマンドで用が足りることでしょう。 -/
