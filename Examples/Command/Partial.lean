/- # partial
`partial` は部分関数(partial function)を定義するための構文です．

Lean では再帰関数も再帰的でない関数と同様に定義できますが，扱いは異なります．再帰的な関数 `f` を定義すると，Lean は `f` がすべての入力に対して必ず有限回の再帰で停止することを証明しようとします．自動的な証明が失敗すると，エラーになってしまいます．エラーを消すには，

* 停止することを手動で証明するか
* 停止性は保証しないと明示的にマークするか

どちらかの対応が必要です．関数の定義に `partial` とマークすると, 停止性は保証しないとマークしたことになります．
-/
namespace WithoutPartial --#

/--
error: fail to show termination for
  WithoutPartial.alternate
with errors
argument #2 was not used for structural recursion
  failed to eliminate recursive application
    alternate ys xs

argument #3 was not used for structural recursion
  failed to eliminate recursive application
    alternate ys xs

structural recursion cannot be used

Could not find a decreasing measure.
The arguments relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            xs ys
1) 38:24-39  ?  ?
Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs (whitespace := lax) in
def alternate {α : Type} (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => ys
  | x :: xs, ys => x :: alternate ys xs

end WithoutPartial --#
namespace Partial --#
-- `partial` を使うと，停止性の証明が不要になる
partial def alternate {α : Type} (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => ys
  | x :: xs, ys => x :: alternate ys xs

#guard alternate [1, 3, 5] [2, 4, 6] = [1, 2, 3, 4, 5, 6]

/- ## 舞台裏
なお，`partial` とマークされた定義を元に新たに関数を定義するとき，再度 `partial` とマークする必要はありません． -/

/-- 階乗っぽいが停止しない関数 -/
partial def forever (x : Int) : Int :=
  if x = 0 then 1
  else x * forever (x - 1)

-- more 関数も停止しないが，partial は不要である
def more := @forever

/- これは意外に思えます．`partial` とマークされた関数は停止性が保証されていないので，それを使用した関数も停止性を保証できなくなるはずだからです．なぜこうなるのかというと，`partial` はそもそも「停止性が保証されていない」ことを表すものではなく，「名前が定義に展開できない」ことを表すものだからです．-/

-- 実際に #reduce を実行してみると，
-- forever の部分が簡約されていないことがわかる
/-- info: forever (Int.ofNat 5) -/
#guard_msgs in #reduce forever 5

/-- 正しい階乗関数 -/
def factorial (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x + 1 => (x + 1) * factorial x

-- 正しい階乗関数と比較してみると，
-- 正しい方は簡約ができていることがわかる
/-- info: 120 -/
#guard_msgs in #reduce factorial 5

/- ## 例外的な挙動
再帰的でない関数に `partial` をマークしても何も起こりません．-/

partial def square (x : Int) := x * x

-- 簡約が実行される
/-- info: Int.ofNat 1024 -/
#guard_msgs in #reduce square 32

end Partial --#
