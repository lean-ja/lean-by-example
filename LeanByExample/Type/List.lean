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

`List` は [`Functor`](#{root}/TypeClass/Functor.md) 型クラスのインスタンスになっているため `<$>` 演算子が利用できます。
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

/- ### foldl と foldr

`List.foldl` と `List.foldr` は、リストの各要素を指定した二項演算で繋げます。
-/

/-- `List.foldl` の例示のための型クラス -/
class Foldl (α β : Type) where
  /-- 左結合的な二項演算 -/
  op : α → β → α

-- 左結合的な演算子として `⊗` を定義する
@[inherit_doc] infixl:70 "⊗" => Foldl.op

/-- #### List.foldl の使用例

デフォルト値が `init : α` で、適用する二項演算が `⊗ : α → β → α` だとする。
また `⊗` は左結合的、つまり `a ⊗ b ⊗ c = (a ⊗ b) ⊗ c` であるとする。
このとき `[b₁, b₂, b₃] : List β` に対して、
`List.foldl` は左にデフォルト値を挿入して順に `⊗` を適用したものに等しい。
-/
example [Foldl α β] {b₁ b₂ b₃ : β} (init : α) :
    [b₁, b₂, b₃].foldl (· ⊗ ·) init = init ⊗ b₁ ⊗ b₂ ⊗ b₃ := by
  rfl

/-- `List.foldr` の例示のための型クラス -/
class Foldr (α β : Type) where
  /-- 右結合的な二項演算 -/
  op : α → β → β

-- 右結合的な演算子として `⋄` を定義する
@[inherit_doc] infixr:70 "⋄" => Foldr.op

/-- #### List.foldr の使用例

デフォルト値が `init : β` で、適用する二項演算が `⋄ : α → β → β` だとする。
また `⋄` は右結合的、つまり `a ⋄ b ⋄ c = a ⋄ (b ⋄ c)` であるとする。
このとき `[a₁, a₂, a₃] : List α` に対して、
`List.foldr` は右にデフォルト値を挿入して順に `⋄` を適用したものに等しい。
-/
example [Foldr α β] {a₁ a₂ a₃ : α} (init : β) :
    [a₁, a₂, a₃].foldr (· ⋄ ·) init = a₁ ⋄ a₂ ⋄ a₃ ⋄ init := by
  rfl

/- `List.foldl` と `List.foldr` の違いは、演算が左結合的と仮定するか右結合的と仮定するか以外にも、`List.foldl` は末尾再帰(tail recursion)であるが `List.foldr` はそうでないことが挙げられます。 -/

/-- 自然数のリストの総和を計算する関数 -/
def List.sum' : List Nat → Nat
  | [] => 0
  | n :: ns => n + sum ns

/-- List.sum は List.foldr で表すことができる -/
example : List.foldr (· + ·) 0 = List.sum := by
  -- 再帰的な定義を分解する
  delta List.foldr List.sum

  -- 両者は等しい
  rfl

/-- 末尾再帰にした総和関数 -/
def List.sumTR (l : List Nat) : Nat :=
  aux 0 l
where
  -- ある初期値から始めてリストの各要素の総和を求めるヘルパ関数
  aux : Nat → List Nat → Nat
  | x, [] => x
  | x, n :: ns => aux (x + n) ns

/-- List.sumTR は List.foldl で表すことができる -/
example : List.foldl (· + ·) 0 = List.sumTR := by
  -- 再帰的な定義を分解する
  delta List.foldl List.sumTR List.sumTR.aux

  -- 両者は等しい
  rfl

/- ## モナドインスタンス

Lean では、`List` は標準で `Monad` 型クラスのインスタンスになっていません。
-/

/--
error: failed to synthesize
  Monad List
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
  #synth Monad List

/- しかし、`Monad` 型クラスのインスタンスにすることは可能です。 -/

instance : Monad List where
  pure := @List.singleton
  map := @List.map
  bind := @List.flatMap

/- `List` のモナドインスタンスを利用すると、「リスト `xs : List α` の中から要素 `x : α` を選んで `y : β` を構成することをすべての要素 `x ∈ xs` に対して繰り返し、結果の `y` を集めてリスト `ys : List β` を構成する」ということができます。 -/

def List.listUp {α β : Type} (xs : List α) (f : α → β) : List β := do
  -- `x ∈ xs` を選ぶ
  let x ← xs

  -- `y := f x` を構成する
  let y := f x

  -- `y : β` を返す。`List.listUp` の結果は、返される `y` を集めたものになる。
  return y

#guard [1, 2, 3].listUp (· + 1) = [2, 3, 4]

#guard [1, 2, 3, 4].listUp (· % 3 == 0) = [false, false, true, false]

/- `List` のモナドインスタンスを利用すると、「選択肢のすべてに対して特定の構成を繰り返して、結果を一つのリストにすべてまとめて返す」系の関数を簡潔に実装できることがあります。 -/

/-- `α` 上の n 項演算全体の型 -/
def Arity (α : Type) : (n : Nat) → Type
  | 0 => α
  | n + 1 => α → Arity α n

/-- 3 項演算 `Bool → Bool → Bool` の例 -/
example : Arity Bool 2 := fun a b => a && b

/-- 真理関数 `p : Arity Bool n` に対して、その真理値表を作成する。-/
def tablen (n : Nat) (p : Arity Bool n) : List (List Bool) :=
  match n with
  | 0 => [[p]]
  | n + 1 => do
    let b ← [true, false]
    let rest ← tablen n (p b)
    return b :: rest

/-- info: [[true, true, true],
  [true, false, false],
  [false, true, false],
  [false, false, false]] -/
#guard_msgs (whitespace := lax) in
  #eval tablen 2 (fun a b => a && b)

-- 結果が false になるものだけ表示
#guard [[false, false, false, false]] =
  (tablen 3 (fun a b c => a || b || c) |>.filter (fun xs => ! xs.getLast!))
