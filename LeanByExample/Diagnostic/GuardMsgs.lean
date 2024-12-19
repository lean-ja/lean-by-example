/-
# \#guard_msgs

`#guard_msgs` コマンドは、あるコマンドの出力が与えられた文字列と一致するか検証します。
-/
import Mathlib.Algebra.Group.Defs -- 逆数を使うために必要 --#

/-- info: 2 -/
#guard_msgs in #eval 2

/--
error: failed to synthesize
  HAdd ℕ String String
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #eval (2 + "hello" : String)

/- ## 空白の違いを無視させるには
`#guard_msgs` コマンドは空白の数に敏感で、空白の長さによって通ったり通らなかったりします。しかし、`whitespace` という引数に `lax` を指定することにより、この空白に関する制限は緩めることができます。
-/

variable (α : Type)

-- 通常の場合
/--
error: failed to synthesize
  Inv α
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #check (_ : α)⁻¹

-- スペースを入れてもエラーにならない
/--
error:
  failed to synthesize
    Inv α
  Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in #check (_ : α)⁻¹
