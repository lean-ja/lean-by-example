/-
# Coe
`Coe` は、型強制(coercion)と呼ばれる仕組みをユーザが定義するための型クラスです。

ある型 `T` が期待される場所に別の型の項 `s : S` を見つけると、Lean は型エラーにする前に自動的に型変換を行うことができないか試します。ここで行われる「自動的な型変換」が型強制です。型強制を明示的に指定するには、`↑` 記号をつけて `↑x` などのようにします。なお `↑` 記号については [`[coe]`](#{root}/Attribute/Coe.md) 属性も深い関係があります。

具体的には `Coe S T` という型クラスのインスタンスが定義されているとき、型 `S` の項が型 `T` に変換されます。

例えば、正の自然数からなる型 `Pos` を定義したとします。包含関係から `Pos → Nat` という変換ができるはずです。この変換を関数として定義するだけでは、必要になるごとに毎回書かなければなりませんが、型強制を使うと自動化することができます。
-/
namespace Coe --#

/-- 正の自然数 -/
inductive Pos where
  | one : Pos
  | succ : Pos → Pos

def one : Pos := Pos.one

/-- 階乗関数 -/
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- `factorial` の引数は `Nat` なのに、`Pos` を渡したのでエラーになる
/--
error: application type mismatch
  factorial one
argument
  one
has type
  Pos : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs (error) in
#check factorial one

/-- `Pos` から `Nat` への変換 -/
def Pos.toNat : Pos → Nat
  | one => 1
  | succ n => n.toNat + 1

-- 明示的に変換すればエラーにならないが、
-- `Pos ⊆ Nat` と見なして自動で変換してほしくなる
#eval factorial <| one.toNat

/-- `Pos` から `Nat` への型強制 -/
instance : Coe Pos Nat where
  coe n := n.toNat

-- 自動的に `Pos` から `Nat` への変換が行われるようになった！
#guard factorial one = 1

end Coe --#
