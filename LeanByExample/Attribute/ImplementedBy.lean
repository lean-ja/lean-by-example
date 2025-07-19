/- # implemented_by

`[implemented_by]` は、仕様（満たしてほしい性質）と実装を分離するための属性です。

`[implemented_by]` 属性を使うと、実行時の実装を証明なしに置き換えてしまうことができます。
-/

def bar := "world"

-- 実行する際には`bar`を参照してくださいとLeanに指定している
@[implemented_by bar]
def foo := "hello"

/-⋆-//-- info: "world" -/
#guard_msgs in --#
#eval foo

/- `[implemented_by]` で置換されるのは実行時の実装であって、証明時のふるまいは変わりません。 -/

-- 証明においては`foo`は`"hello"`のまま
example : foo = "hello" := rfl

/- [`native_decide`](#{root}/Tactic/NativeDecide.md) を使用するなどしてコンパイラを信頼することにすれば、置換した内容を証明に利用することもできます。
しかし、当然ながらこれによって証明の健全性は保証されません。
-/

example : foo = "world" := by
  native_decide
