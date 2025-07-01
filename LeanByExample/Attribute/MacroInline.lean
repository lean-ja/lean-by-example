/- # macro_inline

`[macro_inline]` 属性は、関数に付与することでその関数をマクロのように展開させることができます。これにより、関数の引数の評価が、関数の評価前からそれが最初に使われた時点に延期されます。

## 用途

多くの場合、`[macro_inline]` 属性は短絡評価(short-circuit evaluation)を実装するのに使われます。短絡評価とは、「引数を全て評価するまでもなく値がわかるときには、残りの引数を評価しない」という評価戦略のことです。この評価戦略が実装されている典型的な関数として、論理演算子 `&&` や `||` が挙げられます。
-/

-- 第二引数は評価されていない。
/-⋆-//-- info: false -/
#guard_msgs in --#
#eval false && (dbg_trace "hello"; true)

-- 第二引数は評価されていない。
/-⋆-//-- info: true -/
#guard_msgs in --#
#eval true || (dbg_trace "hello"; true)

/- 実際に `Bool.and`（つまり `&&`）を真似て関数を自作してみて、`[macro_inline]` 属性の挙動を確認してみましょう。 -/

/-- `Bool.and` を真似て自作した関数
(わざと冗長な定義を採用している) -/
def Bool.myAnd : Bool → Bool → Bool
  | false, _ => false
  | true, true => true
  | _, false => false

-- 第二引数が評価されており、短絡評価になっていない
/-⋆-//--
info: hello
---
info: false
-/
#guard_msgs in --#
#eval Bool.myAnd false (dbg_trace "hello"; true)

-- `[macro_inline]` 属性を付与する
attribute [macro_inline] Bool.myAnd

-- 短絡評価になった！！
/-⋆-//-- info: false -/
#guard_msgs in --#
#eval Bool.myAnd false (dbg_trace "hello"; true)
