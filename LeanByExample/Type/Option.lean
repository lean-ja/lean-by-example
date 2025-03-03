/- # Option

`Option` は、失敗するかもしれない計算を表す型です。

`Option` は帰納型として定義されています。`α : Type u` に対して、`Option α` は `some a` または `none` のいずれかの形をした項になっています。`none` は計算が失敗し、値を返せなかったことを表します。
-/
namespace Hidden --#
--#--
/--
info: inductive Option.{u} : Type u → Type u
number of parameters: 1
constructors:
Option.none : {α : Type u} → Option α
Option.some : {α : Type u} → α → Option α
-/
#guard_msgs in
  #print _root_.Option
--#--

inductive Option.{u} (α : Type u) where
  /-- 値が返せないことを意味する。 -/
  | none : Option α
  /-- `α` 型の値を単に包んだもの。 -/
  | some (val : α) : Option α

end Hidden --#
/- ## 典型的な使用例

たとえば、配列 `xs : Array α` に対して、インデックス `i` の要素は存在するとは限りません。`xs` の長さよりも `i` が大きければ、返すべき値がないからです。このため、Lean の標準ライブラリには返り値を `Option` に包んだ関数が用意されています。
-/

-- インデックス 0 の要素は存在するので取得できる
#guard #[1, 2, 3][0]? = some 1

-- インデックス 3 の要素は存在しないので取得できず、none が返ってくる
#guard #[1, 2, 3][3]? = none

/- 配列やリストなどのコレクション型から要素を取り出す類の操作には、多くの場合返り値が `Option` に包まれた関数が用意されます。より詳しくは [`GetElem`](#{root}/TypeClass/GetElem.md) のページを参照してください。 -/

/- ## Functor インスタンス

`Option` は [`Functor`](#{root}/TypeClass/Functor.md) 型クラスのインスタンスであり、`<$>` が使用できます。実装上は `Option.map` が使用されます。
-/
section
  /- ## Functor インスタンスの実装を確かめる例 -/
  variable {α β : Type}

  -- `<$>` は `Option.map` で実装されている
  example (x? : Option α) (f : α → β) : f <$> x? = Option.map f x? := by
    rfl

end
/- `Option.map` は、計算が成功すれば関数を適用し、失敗したら失敗を伝搬します。つまり、`Option.map f x?` は、`x?` が `some x` ならば `some (f x)` を返し、`x?` が `none` ならば `none` を返します。 -/
section
  variable {α β : Type}

  -- `Option.map f` は some x を some (f x) に写す
  example (x : α) (f : α → β) : Option.map f (some x) = some (f x) := by
    rfl

  -- `Option.map f` は none を none に写す
  example (f : α → β) : Option.map f none = none := by
    rfl

end
