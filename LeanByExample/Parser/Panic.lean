/- # panic!

`panic!` を使うと、その部分が実行されたときにエラーメッセージが表示されます。
-/

/-- 0 で割るときに警告を出すような除算関数 -/
def safeDiv (x y : Nat) : Nat :=
  if y = 0 then panic! "0 で割ることはできません！" else x / y

/-⋆-//--
info: PANIC at safeDiv LeanByExample.Parser.Panic:8:16: 0 で割ることはできません！
---
info: 0
-/
#guard_msgs in --#
#eval safeDiv 10 0

/- ## panic! で処理は中断しない

注意点として、`panic!` を使っても処理は中断しません。その部分で期待されている型の [`Inhabited`](#{root}/TypeClass/Inhabited.md) インスタンスが使用されて、値を返します。上記の例でいうと、`Nat` の `Inhabited` インスタンスが使用されて `0` が返ります。
-/

-- エラーメッセージが出るだけで処理は中断されていない
#guard safeDiv 10 0 = 0

/- 処理を本当に中断したい場合、たとえば [`IO`](#{root}/Type/IO.md) モナドで返り値を包んだうえで、例外を `throw` すればよいでしょう。-/

/-- ゼロ除算に対して例外を投げるバージョンの割り算 -/
def divIO (x y : Nat) : IO Nat :=
  if y = 0 then
    throw (IO.userError "0 で割ることはできません！")
  else
    pure (x / y)

/-⋆-//-- error: 0 で割ることはできません！ -/
#guard_msgs in --#
#eval divIO 10 0

/- ## panic! は例外を投げない

`panic!` は例外を投げているわけではなく、`try .. catch` ブロックで補足することはできません。例外ハンドリングが必要な場合は `panic!` を使用しない方が良いでしょう。
-/

/-⋆-//--
info: PANIC at safeDiv LeanByExample.Parser.Panic:8:16: 0 で割ることはできません！
Result: 0
-/
#guard_msgs in --#
#eval show IO Unit from do
  try
    let result := safeDiv 10 0
    IO.println s!"Result: {result}"
  catch e =>
    IO.println s!"Caught an error: {e}"
