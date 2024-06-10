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

/- なお，`partial` とマークされた定義を元に新たに関数を定義するとき，再度 `partial` とマークする必要はありません． -/

def more_alternate := @alternate

end Partial --#
