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
/- ## 再帰と variable

`variable` コマンドで宣言された引数は、再帰呼び出しの中でも同じ値が使用されます。
したがって、再帰関数の再帰呼び出しで変化する引数を `variable` で共通化することはできません。
-/

variable {α : Type} (l : List α)

set_option warn.sorry false in --#
def List.myLength : Nat :=
  match l with
  | [] => 0
  | _ :: xs => by
    -- `List.myLength` の型が `List α → Nat` ではなくて、
    -- `Nat` になってしまっている。
    -- 引数の `List α` の部分には固定された値が入ってしまっているため
    guard_hyp List.myLength : Nat

    sorry
