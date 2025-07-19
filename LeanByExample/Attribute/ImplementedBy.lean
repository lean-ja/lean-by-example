/- # implemented_by

`[implemented_by]` は、仕様（満たしてほしい性質）と実装を分離するための属性です。

`[implemented_by]` 属性を使うと、実行時の実装を証明なしに置き換えてしまうことができます。
-/

def bar := "world"

-- 実行する際には`bar`を参照してくださいとLeanに指定している
@[implemented_by bar]
def foo := "hello"

/-⋆-//-- info: "world" -/
#guard_msgs in --#
#eval foo

/- `[implemented_by]` で置換されるのは実行時の実装であって、証明時のふるまいは変わりません。 -/

-- 証明においては`foo`は`"hello"`のまま
example : foo = "hello" := rfl

/- [`native_decide`](#{root}/Tactic/NativeDecide.md) を使用するなどしてコンパイラを信頼することにすれば、置換した内容を証明に利用することもできます。
しかし、当然ながらこれによって証明の健全性は保証されません。
-/

example : foo = "world" := by
  native_decide

/- ## 使用例

典型的な使用場面として、「[`unsafe`](#{root}/Modifier/Unsafe.md) だが高速なコード」を安全に使用したい場面というのがあります。
たとえば、２分木を考えます。[^bintree]
-/

/-- 2分木 -/
inductive Tree (α : Type) where
  /-- 空の木 -/
  | empty
  /-- 左右の部分木とノードの値から、新しい木を得る -/
  | branch (left : Tree α) (value : α) (right : Tree α)

/- 2分木`t₁ t₂`に対して、`t₁ == t₂` であるかどうかを判定する関数を考えます。
再帰的に判定すればできるのですが、`t₁` と `t₂` のメモリアドレスが等しい場合にはそんなことをするのはムダになります。
そこで、次のような関数を定義します。
-/

/-- 高速だが unsafe な BEq の実装 -/
unsafe def Tree.fastBEq {α : Type} [BEq α] (t₁ t₂ : Tree α) : Bool :=
  -- メモリアドレスが等しいならば、同じ木である
  if ptrEq t₁ t₂ then
    true
  else
    -- それ以外の場合は再帰的に判定する
    match t₁, t₂ with
    | .empty, .empty => true
    | .branch l₁ v₁ r₁, .branch l₂ v₂ r₂ =>
      v₁ == v₂ && fastBEq l₁ l₂ && fastBEq r₁ r₂
    | _, _ => false

/- しかし、`ptrEq` が `unsafe` なので、`Tree.fastBEq` 全体が `unsafe` になってしまいます。
`[implemented_by]` 属性を使うと、実行時には `Tree.fastBEq` を使うというのは維持したまま、証明時には安全な定義を使うことができます。
-/

@[implemented_by Tree.fastBEq]
def Tree.beq {α : Type} [BEq α] (t₁ t₂ : Tree α) : Bool :=
  match t₁, t₂ with
  | .empty, .empty => true
  | .branch l₁ v₁ r₁, .branch l₂ v₂ r₂ =>
    v₁ == v₂ && Tree.beq l₁ l₂ && Tree.beq r₁ r₂
  | _, _ => false

instance {α : Type} [BEq α] : BEq (Tree α) where
  beq := Tree.beq

/-
[^bintree]: このコード例と解説は、[The Lean Language Reference](https://lean-lang.org/doc/reference/latest/) を参考にしています。
-/
