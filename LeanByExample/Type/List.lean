/- # List

`List` は **連結リスト(linked list)** を表す型です。

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

/- ## 先頭への要素の追加
`List α` の先頭に要素を追加した新しいリストを作るのは、コンストラクタ `List.cons` で可能ですが、これには `::` という記法が割り当てられています。
-/

-- List.cons x xs は x :: xs と書ける
example {α : Type} (x : α) (xs : List α) : List.cons x xs = x :: xs := by
  rfl

-- `::` で先頭に要素を追加する
#guard "hello" :: ["world"] = ["hello", "world"]

/- ## 連結
リスト同士を順序を保ちながら連結するには、`List.append` 関数を使います。これは `Append` 型クラスのインスタンスになっているので、`++` という演算子で利用できます。
-/
-- `++` 演算子が利用できる
example {α : Type} (xs ys : List α) : xs ++ ys = List.append xs ys := by
  rfl

-- リストの連結
#guard [1.0, 2.0] ++ [3.0] == [1.0, 2.0, 3.0]

/- ## 高階関数

「関数を引数に取る関数」や「関数を返す関数」のことを、**高階関数(higher-order function)** と呼ぶことがあります。`List` 名前空間には様々な高階関数が定義されています。

### map

`List` は [`Functor`](#{root}/TypeClass/Functor.md) 型クラスのインスタンスになっているため `<$>` 演算子が利用できます。`<$>` は `List.map` で実装されています。
-/

-- `<$>` 演算子が利用できる
#guard (fun x => x * 2) <$> [1, 2, 3] = [2, 4, 6]

example {α β : Type} (f : α → β) (xs : List α) : f <$> xs = List.map f xs := by
  rfl

/- `List.map f` は「リストの中身のそれぞれに独立に関数を適用する」操作を表します。具体的には関数 `f : α → β` があるとき、`List.map f` は関数 `List α → List β` であって、リスト `xs : List α` の各要素に `f` を適用するようなものです。 -/
section

  variable {α β : Type} {a₁ a₂ a₃ : α}

  example (f : α → β) : [a₁, a₂, a₃].map f = [f a₁, f a₂, f a₃] := by
    rfl

  -- リストの各要素を 2 倍する
  #guard List.map (fun x => x * 2) [1, 2, 3] = [2, 4, 6]

end
/- ### filter

`List` の中の要素から、ある条件を満たすものだけを取り出すには `List.filter` を使います。
-/

-- `l` 以外の文字を残す
#guard ["h", "e", "l", "l", "o"].filter (· ≠ "l") = ["h", "e", "o"]

-- 偶数を残す
#guard [1, 2, 3, 4, 5].filter (· % 2 = 0) = [2, 4]

/- ### foldr

`List.foldr` は、右結合的な二項演算でリストの各要素を繋げて畳み込む(fold)関数です。
-/

/-- `List.foldr` の例示のための型クラス -/
class Foldr (α β : Type) where
  /-- 右結合的な二項演算 -/
  op : α → β → β

-- 右結合的な演算子として `⋄` を定義する
@[inherit_doc] infixr:70 "⋄" => Foldr.op

section
  variable {α β : Type} [Foldr α β] {a₁ a₂ a₃ : α}

  -- foldr を適用することは、リストの要素を二項演算で繋げることに等しい
  example (init : β) : [a₁, a₂, a₃].foldr (· ⋄ ·) init = a₁ ⋄ a₂ ⋄ a₃ ⋄ init := by
    rfl

end
/- `List.foldr` は、多くの再帰関数に共通に現れる再帰のパターンを抽象化したものになっています。たとえば、リストの長さを求める関数 `List.length` を次のように定義すると、これは `List.foldr` の具体例になっています。[^prohaskell] -/
namespace Foldr
  variable {α : Type}

  /-- リストの長さを求める -/
  def length (xs : List α) : Nat :=
    match xs with
    | [] => 0
    | _ :: xs => 1 + length xs

  #guard length [1, 2, 3, 4, 5] = 5

  -- length は foldr で表すことができる！
  example (xs : List α) : length xs = xs.foldr (fun _ n => 1 + n) 0 := by
    delta length List.foldr
    rfl

end Foldr
/- また、リストの順番を逆にする関数 `List.reverse` を次のように定義すると、これも `List.foldr` の具体例になっています。-/
namespace Foldr
  variable {α : Type}

  /-- リストの順番を逆にする関数 -/
  def reverse : List α → List α
    | [] => []
    | x :: xs => reverse xs ++ [x]

  #guard reverse [1, 2, 3, 4, 5] = [5, 4, 3, 2, 1]

  -- reverse は foldr で表すことができる！
  example (xs : List α) : reverse xs = xs.foldr (fun x xs => xs ++ [x]) [] := by
    delta reverse List.foldr
    rfl

end Foldr
/- ### foldl

`List.foldl` は、左結合的な二項演算でリストの各要素を繋げて畳み込む関数です。
-/
/-- `List.foldl` の例示のための型クラス -/
class Foldl (α β : Type) where
  /-- 左結合的な二項演算 -/
  op : α → β → α

-- 左結合的な演算子として `⊗` を定義する
@[inherit_doc] infixl:70 "⊗" => Foldl.op

section
  variable {α β : Type} [Foldl α β] {b₁ b₂ b₃ : β}

  -- foldl を適用することは、リストの要素を二項演算で繋げることに等しい
  example (init : α) : [b₁, b₂, b₃].foldl (· ⊗ ·) init = init ⊗ b₁ ⊗ b₂ ⊗ b₃ := by
    rfl
end
/- `List.foldl` も `List.foldr` と同様、多くの再帰関数に共通に現れる再帰のパターンを抽象化したものになっていますが、`List.foldr` とは異なり **末尾再帰(tail recursion)** になります。たとえば、リストの長さを求める関数 `List.lengthTR` を次のように定義すると、これは `List.foldl` の具体例になっています。 -/
namespace Foldl
  variable {α : Type}

  /-- リストの長さを求める -/
  def lengthTR (xs : List α) : Nat :=
    aux xs 0
  where
    /-- リストの長さを求めるヘルパ関数 -/
    aux : List α → Nat → Nat
      | [], n => n
      | _ :: xs, n => aux xs (1 + n)

  #guard lengthTR [1, 2, 3, 4, 5] = 5

  -- lengthTR は foldl で表すことができる！
  example (xs : List α) : lengthTR xs = xs.foldl (fun n _ => 1 + n) 0 := by
    delta lengthTR lengthTR.aux List.foldl
    rfl

end Foldl
/- また、リストの順番を逆にする関数 `List.reverseTR` を次のように定義すると、これも `List.foldl` の具体例になっています。 -/
namespace Foldl

  variable {α : Type}

  /-- リストの順番を逆にする関数 -/
  def reverseTR (xs : List α) : List α :=
    aux xs []
  where
    /-- リストの順番を逆にするヘルパ関数 -/
    aux : List α → List α → List α
      | [], acc => acc
      | x :: xs, acc => aux xs (x :: acc)

  #guard reverseTR [1, 2, 3, 4, 5] = [5, 4, 3, 2, 1]

  -- reverseTR は foldl で表すことができる！
  example (xs : List α) : reverseTR xs = xs.foldl (fun xs x => x :: xs) [] := by
    delta reverseTR reverseTR.aux List.foldl
    rfl

end Foldl
/- ## モナドインスタンス

Lean では、`List` は標準で `Monad` 型クラスのインスタンスになっていません。
-/

#check_failure (inferInstance : Monad List)

/- しかし、`Monad` 型クラスのインスタンスにすることは可能です。 -/

instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

/- `List` のモナドインスタンスを利用すると、「リスト `xs : List α` の中から要素 `x : α` を選んで `y : β` を構成することをすべての要素 `x ∈ xs` に対して繰り返し、結果の `y` を集めてリスト `ys : List β` を構成する」ということができます。 -/

def List.map' {α β : Type} (xs : List α) (f : α → β) : List β := do
  -- `x ∈ xs` を選ぶ
  let x ← xs

  -- `y := f x` を構成する
  let y := f x

  -- `y : β` を返す。関数全体の返り値は、返される `y` を集めたものになる。
  return y

#guard [1, 2, 3].map' (· + 1) = [2, 3, 4]

#guard [1, 2, 3, 4].map' (· % 3 == 0) = [false, false, true, false]

/- `List` のモナドインスタンスを利用すると、「選択肢のすべてに対して特定の構成を繰り返して、結果を一つのリストにすべてまとめて返す」系の関数を簡潔に実装できることがあります。 -/

/-- `α` 上の n 項演算全体の型 -/
def Arity (α : Type) : (n : Nat) → Type
  | 0 => α
  | n + 1 => α → Arity α n

/-- 2 項演算 `Bool → Bool → Bool` の例 -/
example : Arity Bool 2 := fun a b => a && b

/-- 真理関数 `p : Arity Bool n` に対して、その真理値表を作成する。-/
def tablen (n : Nat) (p : Arity Bool n) : List (List Bool) :=
  match n with
  | 0 => [[p]]
  | n + 1 => do
    let b ← [true, false]
    let rest ← tablen n (p b)
    return b :: rest

#guard
  let expected := [
    [true, true, true],
    [true, false, false],
    [false, true, false],
    [false, false, false]
  ]
  let actual := tablen 2 (fun a b => a && b)
  expected = actual

#guard
  let result := tablen 3 (fun a b c => a || b || c)

  -- 結果が false になるものだけ集める
  result.filter (fun xs => ! xs.getLast!) = [[false, false, false, false]]

/- [^prohaskell] ここで使用した例は、Graham Hutton著, 山本和彦訳「Programming Haskell 第2版」（ラムダノート）の7.3章を参考にさせていただきました。 -/
