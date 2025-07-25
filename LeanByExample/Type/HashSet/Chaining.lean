import Lean

open Std

namespace Playground

variable {α : Type} [Hashable α] [BEq α]

/-- チェイン法（chaining）による HashSet の実装 -/
structure HashSet (α : Type) where
  /-- 内部データとしての配列 -/
  data : Array (List α)
  /-- data のサイズ -/
  size : Nat

/-- 空の HashSet。空リストばかり格納されている。 -/
def HashSet.empty (size := 10000) : HashSet α :=
  { size := size, data := Array.replicate size [] }

/-- UInt64 を Nat に自動で変換する -/
instance : Coe UInt64 Nat where
  coe n := n.toNat

/-- HashSet に新しい要素を挿入する -/
def HashSet.insert (s : HashSet α) (x : α) : HashSet α :=
  -- 内部にある配列を取得する
  let data := s.data

  -- 加えようとしている要素のハッシュ値を計算して、
  -- それをインデックスとして内部の配列にアクセスする
  let idx := hash x
  let list : List α := data[(idx : Nat) % data.size]!

  -- 既に x が存在する場合とそうでない場合で場合分けをする
  if list.contains x then
    -- 既に存在する場合はそのままの HashSet を返す
    s
  else
    -- 存在しない場合
    -- そのインデックスにあるリストに要素を追加する
    let newData := data.set! idx (x :: list)

    -- 新しいデータを持つ HashSet を返す
    { size := data.size, data := newData }

/-- HashSet に要素があるか判定する。
ハッシュ関数でインデックスを計算するので高速に判定できる。-/
def HashSet.contains (s : HashSet α) (x : α) : Bool :=
  -- 内部にある配列を取得する
  let data := s.data

  -- 加えようとしている要素のハッシュ値を計算して、
  -- それをインデックスとして内部の配列にアクセスする
  let idx := hash x
  let list : List α := data[(idx : Nat) % data.size]!

  -- そのリストに x が含まれているかどうかを返す
  list.contains x

/-- HashSet から要素を削除する。
ハッシュ関数の値でインデックスがわかるので高速に削除できる。-/
def HashSet.erase (s : HashSet α) (x : α) : HashSet α :=
  -- 内部にある配列を取得する
  let data := s.data

  -- 加えようとしている要素のハッシュ値を計算して、
  -- それをインデックスとして内部の配列にアクセスする
  let idx := hash x
  let list : List α := data[(idx : Nat) % data.size]!

  -- x が存在しない場合はそのままの HashSet を返す
  if !list.contains x then
    s
  else
    -- 存在する場合は、x を除いたリストを作成して新しい HashSet を返す
    let newData := data.set! idx (list.erase x)
    { size := data.size, data := newData }

/-- HashSet をリストに変換する -/
def HashSet.toList (s : HashSet α) : List α := Id.run do
  let mut result : List α := []

  -- 内部の配列をすべて結合してリストにする
  -- ここで、結合するのは `s.size` までの部分だけで良いことに注意
  -- それ以降の部分は全部空リストだとあらかじめわかっている
  for i in [0:s.size] do
    result := s.data[i]! ++ result
  return result

-- contains 関数のテスト
#guard show Bool from Id.run do
  let mut set : HashSet Nat := HashSet.empty
  set := set.insert 1
  set := set.insert 2
  set.contains 1

-- 削除のテスト
#guard show Bool from Id.run do
  let mut set : HashSet Nat := HashSet.empty
  -- 1 を２回挿入
  set := set.insert 1
  set := set.insert 1
  -- 1 を削除する
  set := set.erase 1
  ! set.contains 1

/-⋆-//-- info: [2, 1] -/
#guard_msgs in --#
#eval show (List Nat) from Id.run do
  let mut set : HashSet Nat := HashSet.empty
  -- 1 を２回挿入
  set := set.insert 1
  set := set.insert 1
  set := set.insert 2
  -- HashSet をリストに変換して返す
  set.toList

end Playground
