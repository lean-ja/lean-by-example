/- # List

`List` は**連結リスト**を表す型です。

Lean では次のように再帰的に定義されています。
-/
namespace Hidden --#
--#--
-- 参照しているコードが変わっていないことを確認するためのコード
/--
info: inductive List.{u} : Type u → Type u
number of parameters: 1
constructors:
List.nil : {α : Type u} → List α
List.cons : {α : Type u} → α → List α → List α
-/
#guard_msgs in #print List
--#--

/-- `α` 型の項を集めたリスト -/
inductive List.{u} (α : Type u) where
  /-- 空リスト `[]` はリスト -/
  | nil : List α

  /-- `a : α` と `l : List α` があるとき、`a` を先頭に追加したリストが作れる -/
  | cons (head : α) (tail : List α) : List α

end Hidden --#
/- `List α` の項はカンマ区切りの値を `[]` で囲むことによって作ることができます。-/

#check ([1, 2, 3] : List Nat)

/- ## 要素の追加
`List α` の先頭に要素を追加した新しいリストを作るのは、`::` という記法を使って行うことができます。
-/

-- `::` で先頭に要素を追加する
#guard "hello" :: ["world"] = ["hello", "world"]

/- この操作は元のリストを変更しません。Lean は純粋関数型プログラミング言語であるため、一般にグローバル変数に対して破壊的な変更はできません。今後特に断らない限り、常に元のデータは変更されていないと思ってください。-/

#eval show IO Unit from
  let xs := [1, 2, 3]

  -- 先頭に 0 を追加
  let _ys := 0 :: xs

  -- xs は変更されていない
  assert! xs = [1, 2, 3]

  return ()

/- ## 連結
リスト同士を順序を保ちながら連結するには、`List.append` 関数を使います。これには `++` という演算子が割り当てられています。
-/

-- リストの連結
#guard [1.0, 2.0] ++ [3.0] == [1.0, 2.0, 3.0]

/- ## 高階関数

「関数を引数に取る関数」や「関数を返す関数」のことを、**高階関数**と呼ぶことがあります。`List` 名前空間には様々な高階関数が定義されています。

### map

`List` は `Functor` 型クラスのインスタンスになっているため `<$>` 演算子が利用できます。
-/

-- `<$>` 演算子が利用できる
#guard (fun x => x * 2) <$> [1, 2, 3] = [2, 4, 6]

/- `f <$> xs` は `List` においては `List.map f xs` と解釈され、これは「リストの中身全部に関数を適用する」操作を表します。-/

variable {α β : Type}

/-- #### List.map の使用例

`xs.map f` は、関数 `f : α → β` をリスト `xs : List α` の各要素に適用して、
新しく `List β` の項を作る。
-/
example {a₁ a₂ a₃ : α} (f : α → β)
    : [a₁, a₂, a₃].map f = [f a₁, f a₂, f a₃] := by
  rfl

-- リストの各要素を 2 倍する
#guard List.map (fun x => x * 2) [1, 2, 3] = [2, 4, 6]

/- ### filter

`List` の中の要素から、ある条件を満たすものだけを取り出すには `List.filter` を使います。
-/

-- `l` 以外の文字を残す
#guard ["h", "e", "l", "l", "o"].filter (· ≠ "l") = ["h", "e", "o"]

-- 偶数を残す
#guard [1, 2, 3, 4, 5].filter (· % 2 = 0) = [2, 4]

/- ### foldl

引数に `List α` の項を取る関数は、リストに対する再帰を使って定義されることが多いものです。たとえば、リストの各要素を足し合わせる関数は次のように定義できます。
-/

/-- 自然数のリストに対して、その総和を計算する -/
def List.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + xs.sum

#guard [1, 2, 3, 4].sum = 10

/- これが「各要素を足し合わせる」ではなくて「積を計算する」なら次のようになります。-/

/-- 自然数のリストに対して、その積を計算する -/
def List.prod : List Nat → Nat
  | [] => 1
  | x :: xs => x * xs.prod

#guard [1, 2, 3, 4].prod = 24

/- この二つの関数は初期値と、適用する二項演算だけが異なり、後は一致しています。そこでこの共通する部分を抜き出したのが `List.foldl` です。`List.foldl` はリストを消費しながら二項演算を適用していき、最終的な結果を返します。
-/

/-- `List.foldl` の例示のための型クラス -/
class Foldl (α β : Type) where
  /-- 左結合的な二項演算 -/
  op : α → β → α

-- 左結合的な演算子として `⊗` を定義する
@[inherit_doc] infixl:70 "⊗" => Foldl.op

/-- #### List.foldl の使用例

初期値が `init : α` で、適用する二項演算が `⊗ : α → β → α` だとする。
また `⊗` は左結合的、つまり `a ⊗ b ⊗ c = (a ⊗ b) ⊗ c` であるとする。
このとき `[b₁, b₂, b₃] : List β` に対して、
`List.foldl` は左に初期値を挿入して順に `⊗` を適用したものに等しい。
-/
example [Foldl α β] {b₁ b₂ b₃ : β} (init : α) :
    [b₁, b₂, b₃].foldl (· ⊗ ·) init = init ⊗ b₁ ⊗ b₂ ⊗ b₃ := by
  rfl

-- 総和を foldl で計算した例
#guard [1, 2, 3, 4].foldl (· + ·) 0 = 10

-- 積を foldl で計算した例
#guard [1, 2, 3, 4].foldl (· * ·) 1 = 24

-- リストの最大値を foldl で求める例
#guard [1, 2, 3, 4].foldl (max · ·) 0 = 4

/- ### foldr
`List.foldr` は `List.foldl` の右結合バージョンです。
-/

/-- `List.foldr` の例示のための型クラス -/
class Foldr (α β : Type) where
  /-- 右結合的な二項演算 -/
  op : α → β → β

-- 右結合的な演算子として `⋄` を定義する
@[inherit_doc] infixr:70 "⋄" => Foldr.op

/-- #### List.foldr の使用例

初期値が `init : β` で、適用する二項演算が `⋄ : α → β → β` だとする。
また `⋄` は右結合的、つまり `a ⋄ b ⋄ c = a ⋄ (b ⋄ c)` であるとする。
このとき `[a₁, a₂, a₃] : List α` に対して、
`List.foldr` は右に初期値を挿入して順に `⋄` を適用したものに等しい。
-/
example [Foldr α β] {a₁ a₂ a₃ : α} (init : β) :
    [a₁, a₂, a₃].foldr (· ⋄ ·) init = a₁ ⋄ a₂ ⋄ a₃ ⋄ init := by
  rfl
