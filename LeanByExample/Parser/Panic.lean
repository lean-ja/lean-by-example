/- # panic!

`panic!` を使うと、その部分が実行されたときにエラーメッセージが表示されます。
-/

/-- 0 で割るときに警告を出すような除算関数 -/
def safeDiv (x y : Nat) : Nat :=
  if y = 0 then panic! "0 で割ることはできません！" else x / y

#eval safeDiv 10 0

/- 注意点として、`panic!` を使ったところで**処理は中断しませんし、例外にもなりません**。その部分で期待されている型の [`Inhabited`](#{root}/TypeClass/Inhabited.md) インスタンスが使用されて、値を返してしまいます。上記の例でいうと、`Nat` の `Inhabited` インスタンスが使用されて `0` が返ります。
-/

-- 例外になっておらず、処理は中断されていない
#guard safeDiv 10 0 = 0

/- 処理を本当に中断したい場合、たとえば [`IO`](#{root}/Type/IO.md) モナドで返り値を包んだうえで、例外を `throw` すればよいです。(Lean は純粋関数型言語なので、返り値の型が例外を許していなければ、関数が値を返さずに途中で中断することは許されません) -/

def divIO (x y : Nat) : IO Nat :=
  if y = 0 then
    throw (IO.userError "0 で割ることはできません！")
  else
    pure (x / y)

/-⋆-//-- error: 0 で割ることはできません！ -/
#guard_msgs in --#
#eval divIO 10 0
