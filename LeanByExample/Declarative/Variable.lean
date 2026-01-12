/-
# variable
`variable` は、定理や関数の引数を宣言するためのコマンドです。

たとえば以下の関数と命題に対して、引数の `α : Type` と `l : List α` は共通です。
-/
namespace variable0 --#

/-- リストが空であるか判定する -/
def isNil {α : Type} (l : List α) : Bool :=
  match l with
  | [] => true
  | _ => false

theorem nng_list_length {α : Type} (l : List α) : l.length ≥ 0 := by simp

end variable0 --#

/- `variable` コマンドを利用すると、共通の引数を宣言してまとめておくことができます。-/
namespace variable1 --#

variable {α : Type} (l : List α)

def isNil : Bool :=
  match l with
  | [] => true
  | _ => false

theorem nng_list_length : l.length ≥ 0 := by simp

end variable1 --#
