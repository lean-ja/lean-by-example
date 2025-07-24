/- # HashSet

`Std.HashSet` は、「重複のない集まり」を表すデータ構造です。

`insert` 関数で要素を挿入することができますが、同じ要素を複数回挿入しても１つしか保持されません。
-/
import Lean

open Std

/-⋆-//-- info: Std.HashSet.ofList [1] -/
#guard_msgs in --#
#eval show (HashSet Nat) from Id.run do
  -- 空の `HashSet` を作成
  let mut s : HashSet Nat := {}
  -- `1` を２回挿入
  s := s.insert 1
  s := s.insert 1
  s

/- ## 特長

基本的なコレクション型である [`List`](#{root}/Type/List.md) と比較すると、`HashSet` には「要素が存在するか判定するのが高速」という特徴があります。

`List` では要素を順にたどって調べる必要があるのでサイズに対して線形時間かかってしまう一方で、`HashSet` は（良いハッシュ関数が与えられているという条件下で、平均的に）定数時間で判定することができます。実際に実験して `List` より高速であることを確かめたのが次のコードです。

{{#include ./HashSet/Contain.md}}
-/

/- ## 使用例 -/

/- ### 足して 0 になるペアがあるか判定する

整数からなるリスト `l : List Int` が与えられたとします。このとき、`l` の中に足して 0 になるペアが存在するかどうかを判定する問題を考えます。

この問題は `HashSet` を使うと次のように `O(|l|)` 時間で解くことができます。要素が存在するかどうかを判定するのが高速という特徴が生かされていることに注目してください。もし `List` を使っていたら、要素が存在するかどうかの判定に `Ω(|l|)` 時間かかってしまうので、全体で `Ω(|l|²)` 時間かかってしまいます。
-/

def findSumZeroPair (l : List Int) : Bool := Id.run do
  -- 今までに見た要素を保持するための HashSet
  let mut seen : HashSet Int := {}

  for x in l do
    -- x の補数を既に見つけていたら true を返す
    if seen.contains (-x) then
      return true

    -- そうでなければ、単に x を HashSet に追加して次へ
    seen := seen.insert x

  return false

/- ### 文字列の部分文字列を重複を除いて全列挙する

文字列 `s := c₀c₁..cₙ` に対して、`s` に含まれる連続する文字列 `cₖcₖ₊₁..cₗ` を「`s` の部分文字列」といいます。

与えられた `s : String` に対して、`s` のすべての部分文字列を求める関数を考えます。このとき、部分文字列をどう数えるかの流儀が少なくとも２通り考えられます。

* `s` から切り出す位置が異なっていても、文字列として同じならば部分文字列としても同じ
* `s` から切り出す位置が異なっていれば、部分文字列として異なる

前者の解釈を採用したとするなら、その関数の型は `String → HashSet String` であるべきです。そうすれば型からより多くの情報が得られるほか、重複を除くための処理が簡潔になるからです。
-/

/-- ある文字列の部分文字列を重複を除いて全列挙する -/
def allSubstrings (s : String) : HashSet String := Id.run do
  let mut result : HashSet String := {}
  for j in [1 : s.length + 1] do
    for i in [0 : j] do
      let sub := s.extract ⟨i⟩ ⟨j⟩
      result := result.insert sub
  return result.insert ""
