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
/-
`variable` コマンドを利用すると、共通の引数を宣言してまとめておくことができます。
-/
namespace variable1 --#

variable {α : Type} (l : List α)

def isNil : Bool :=
  match l with
  | [] => true
  | _ => false

theorem nng_list_length : l.length ≥ 0 := by simp

end variable1 --#
/- ## theorem と def での取り込み基準の違い

`variable` コマンドの挙動は [`theorem`](#{root}/Declarative/Theorem.md) と [`def`](#{root}/Declarative/Def.md) で異なります。

[`theorem`](#{root}/Declarative/Theorem.md) コマンドに対しては、定理の型（つまり主張）に現れる変数だけを自動で引数にします。
一方で、[`def`](#{root}/Declarative/Def.md) コマンドに対しては、本体に現れる変数も自動で引数にします。
-/
namespace variable2 --#

variable (n : Nat)

-- 定理の主張には `m` しか現れていないので、`n` は引数として取り込まれない
/-⋆-//--
error: Unknown identifier `n`
-/
#guard_msgs (substring := true) in --#
theorem foo (m : Nat) : m = m :=
  have : n = n := by rfl
  rfl

-- 引数は１つだけ
#check (foo : ∀ m : Nat, m = m)

-- `n` は証明の中にしか現れないが、引数として取り込まれる
def foo' (m : Nat) : m = m :=
  have : n = n := by rfl
  rfl

-- その証拠に `foo'` には引数が２つある
#check (foo' : ∀ (_n m : Nat), m = m)

end variable2 --#
/-
明示的に引数に含めるには、`include` コマンドを使用します。
-/
namespace variable3 --#

variable (n : Nat)

include n

theorem foo_included (m : Nat) : m = m :=
  have : n = n := by rfl
  rfl

-- `n` が引数として含まれた結果
-- 引数が２つになっている
#check (foo_included : ∀ (_n m : Nat), m = m)

end variable3 --#
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
