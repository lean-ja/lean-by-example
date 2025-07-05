/- # partial
`partial` は部分関数(partial function)を定義するための修飾子です。部分関数とは、全ての入力に対しては必ずしも停止しないような関数のことです。

Lean では再帰関数も再帰的でない関数と同様に定義できますが、扱いは異なります。再帰的な関数 `f` を定義すると、Lean は `f` がすべての入力に対して必ず有限回の再帰で停止することを証明しようとします。自動的な証明が失敗すると、エラーになってしまいます。エラーを消すには、以下のどちらかの対応が必要です。

* 停止することを手動で証明するか。
* 停止性は保証しないと明示的にマークするか。

関数の定義に `partial` とマークすると、停止性は保証しないとマークしたことになります。
-/
namespace WithoutPartial --#

-- 何も指定しないと、停止することが Lean にはわからないのでエラーになる
/-⋆-//--
error: fail to show termination for
  WithoutPartial.M
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    M (n + 11)


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n #1
1) 41:7-17 ?  ≤
2) 41:4-18 _  ?

#1: 100 - n

Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in --#
/-- McCarthy の 91 関数 -/
def M (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    M (M (n + 11))

end WithoutPartial --#

-- `partial` を使うと、停止性の証明が不要になる
partial def M (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    M (M (n + 11))

#eval M 91

/- ## 舞台裏
なお、`partial` とマークされた定義を元に新たに関数を定義するとき、再度 `partial` とマークする必要はありません。 -/

/-- 階乗っぽいが停止しない関数 -/
partial def forever (x : Int) : Int :=
  if x = 0 then 1
  else x * forever (x - 1)

-- more 関数も停止しないが、partial は不要である
def more := @forever

/- これは意外に思えます。`partial` とマークされた関数は停止性が保証されていないので、それを使用した関数も停止性を保証できなくなるはずだからです。なぜこうなるのかというと、`partial` はそもそも「停止性が保証されていない」ことを表すものではなく、[`opaque`](#{root}/Declarative/Opaque.md) と同様に「名前が定義に展開できない」ことを表すものだからです。-/

-- 実際に #reduce を実行してみると、
-- forever の部分が簡約されていないことがわかる
/-⋆-//-- info: forever (Int.ofNat 5) -/
#guard_msgs in --#
#reduce forever 5

/-- 正しい階乗関数 -/
def factorial (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x + 1 => (x + 1) * factorial x

-- 正しい階乗関数と比較してみると、
-- 正しい方は簡約ができていることがわかる
/-⋆-//-- info: 120 -/
#guard_msgs in --#
#reduce factorial 5

/- ## 例外的な挙動
再帰的でない関数に `partial` をマークしても何も起こりません。-/

partial def square (x : Int) := x * x

-- 簡約が実行される
/-⋆-//-- info: Int.ofNat 1024 -/
#guard_msgs in --#
#reduce square 32
