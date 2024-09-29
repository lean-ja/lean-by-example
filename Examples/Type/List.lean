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

/-- #### `List.map` の使用例

`xs.map f` は、関数 `f : α → β` をリスト `xs : List α` の各要素に適用して、
新しく `List β` の項を作る。
-/
example {a₁ a₂ a₃ : α} (f : α → β)
    : [a₁, a₂, a₃].map f = [f a₁, f a₂, f a₃] := by
  rfl

-- リストの各要素を 2 倍する
#guard List.map (fun x => x * 2) [1, 2, 3] = [2, 4, 6]

