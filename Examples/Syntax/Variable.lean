/-
# variable
`variable` は，定理や関数の引数を宣言するための構文です．

たとえば以下の関数と命題に対して，引数の `α : Type` と `l : List α` は共通です．
-/
namespace variable0 --#

/-- 連結リストの最後の要素を取り出す -/
def last? {α : Type} (l : List α) : Option α :=
  match l with
  | [] => none
  | [a] => some a
  | _ :: xs => last? xs

theorem nng_list_length {α : Type} (l : List α) : l.length >= 0 := by simp

end variable0 --#

/- `variable` コマンドを利用すると，共通の引数を宣言してまとめておくことができます．-/
namespace variable1 --#

variable {α : Type} (l : List α)

/-- 連結リストの最後の要素を取り出す -/
def last? (l : List α) : Option α :=
  match l with
  | [] => none
  | [a] => some a
  | _ :: xs =>last? xs

theorem nng_list_length : l.length >= 0 := by simp

/- 上記の２つの例で引数の `l : List α` を省略できるかどうかに違いがありますが，これは返り値の型に現れているかどうかに依ります． -/

end variable1 --#
