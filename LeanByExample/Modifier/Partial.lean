/- # partial

`partial` は、Lean による再帰関数の停止性チェックを「停止性を証明することなく」抑制するための修飾子です。おそらく部分関数(partial function)に名前の由来があります。部分関数とは、ある入力に対しては停止しないような関数のことです。

Lean では再帰関数も再帰的でない関数と同様に定義できますが、扱いは異なります。再帰的な関数 `f` を定義すると、Lean は `f` がすべての入力に対して必ず有限回の再帰で停止することを証明しようとします。自動的な証明が失敗すると、エラーになってしまいます。（そもそもなぜ部分関数が許可されないのかについては[部分関数を禁止するのはなぜか？](#{root}/Modifier/DecreasingBy.md#PartialNotAllowed)を参照のこと。）
-/
namespace WithoutPartial --#

-- 何も指定しないと、停止することが Lean にはわからないのでエラーになる
/--
error: fail to show termination for
  WithoutPartial.M
-/
#guard_msgs (substring := true) in --#
/-- McCarthy の 91 関数 -/
def M (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    M (M (n + 11))

end WithoutPartial --#
/-
エラーを消すには、以下のどちらかの対応が必要です。

* 停止することを手動で証明するか。
* 停止性は保証しないと明示的にマークするか。

関数の定義に `partial` とマークすると、停止性は保証しないとマークしたことになります。
-/


-- `partial` を使うと、停止性の証明が不要になる
partial def M (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    M (M (n + 11))

#eval M 91

/- ## partial が使えないケース

どんな再帰関数 `f : A → B` でも `partial` を使えば定義を通せるようになるわけではありません。
関数型 `A → B` が空でないことがそもそも保証されていない場合、`f : A → B` の存在を認めただけで矛盾が起きるので `partial` は使えません。
そのような場合でも定義を通すには、[`unsafe`](./Unsafe.md) を使用するとよいでしょう。
-/

variable {α : Type} in

-- エラーになってしまう
--#--
/--
error: failed to compile 'partial' definition `findSome`, could not prove that the type
  {α : Type} → (Nat → Option α) → Nat → α
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type, while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs (error) in
--#--
partial def findSome (as : Nat → Option α) (start : Nat) : α :=
  match as start with
  | some x => x
  | none => findSome as (start + 1)

/- ## 舞台裏

なお、`partial` とマークされた定義を元に新たに関数を定義するとき、再度 `partial` とマークする必要はありません。 -/

/-- 階乗っぽいが停止しない関数 -/
partial def forever (x : Int) : Int :=
  if x = 0 then 1
  else x * forever (x - 1)

-- more 関数も停止しないが、partial は不要である
def more := @forever

/- これは意外に思えます。`partial` とマークされた関数は停止性が保証されていないので、それを使用した関数も停止性を保証できなくなるはずだからです。なぜこうなるのかというと、`partial` はそもそも「停止性が保証されていない」ことを表すものではなく、[`opaque`](#{root}/Declarative/Opaque.md) コマンドと同様に「名前が定義に展開できない」ことを表すものだからです。-/

-- 実際に #print してみると、`opaque` と表示される
/-- info: opaque forever : Int → Int -/
#guard_msgs in --#
#print forever

/-- 正しい階乗関数 -/
def factorial (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x + 1 => (x + 1) * factorial x

-- 正しい階乗関数と比較してみると、
-- 正しい方は `opaque` ではなく、中身が表示されることがわかる
/--
info: def factorial : Nat → Nat :=
fun x => Nat.brecOn x factorial._f
-/
#guard_msgs in --#
#print factorial

/-
ある関数・定数が `partial` な関数に依存しているかチェックしたい場合は、`#print opaque` コマンドを使用することでできます。

{{#include ./Partial/PrintOpaque.md}}
-/

/- ## 例外的な挙動

再帰的でない関数を `partial` とマークしても何も起こりません。-/

partial def square (x : Int) := x * x

-- 簡約が実行される
/-- info: Int.ofNat 1024 -/
#guard_msgs in --#
#reduce square 32
