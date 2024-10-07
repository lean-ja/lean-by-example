/- # 全射・単射と左逆・右逆写像

関数 `f : A → B` が**全射**であるとは、任意の `b : B` に対して `f a = b` となる `a : A` が存在することをいいます。また、`f` が**単射**であるとは、任意の `a₁, a₂ : A` に対して `f a₁ = f a₂` ならば `a₁ = a₂` となることをいいます。

これを Lean で表現すると次のようになります。
-/
set_option autoImplicit false --#
set_option relaxedAutoImplicit false --#

variable {A B : Type}

/-- 関数の全射性 -/
def Function.Surjective (f : A → B) : Prop := ∀ b, ∃ a, f a = b

/-- 関数の単射性 -/
def Function.Injective (f : A → B) : Prop := ∀ {a₁ a₂ : A}, f a₁ = f a₂ → a₁ = a₂

/- 一見すると、全射と単射はペアになる概念とは思えないかもしれません。束縛変数の数も違いますし、意味上もまったく独立した概念のように見えます。

しかし、`A` が空でないと仮定すれば、選択原理 [`Classical.choice`](#{root}/Reference/Declarative/Axiom.md#ClassicalChoice) を使うことによって、全射 `f : A → B` があれば逆方向の単射 `g : B → A` が構成でき、逆に単射 `f : A → B` があれば逆方向の全射 `g : B → A` を構成することができます。

ある意味で、全射と単射はペアをなす概念であると言えるかもしれないですね。今回の演習問題のテーマはこの定理です。
-/

/- ## 問1: 全射から逆方向の単射
まずは、全射 `f : A → B` が存在すれば逆方向の単射 `g : B → A` も存在することを示しましょう。

実際にはより強く、`f ∘ g = id` を満たすような `g` が構成できます。一般に、`f ∘ g = id` が成り立つとき、`g` を `f` の右逆写像であるとか、切断(section)であるとかいいます。
-/

-- 選択原理を使用する
open Function Classical

/-- 全射 `f : A → B` があれば、選択原理を使用することにより
単射 `g : B → A` を作ることができる。-/
theorem surj_to_inj (f : A → B) (hsurj : Surjective f)
    : ∃ g : B → A, Injective g := by
  -- まず `g` を構成する。
  -- 任意の `b : B` に対して `f` の全射性より
  -- `f a = b` となる `a : A` が存在するのでそれを返す。
  let g : B → A := fun b => sorry

  -- `g` の定義と `f` の全射性から、`f (g b) = b` が成り立つ。
  have gdef : ∀ b, f (g b) = b := by
    sorry

  -- `f ∘ g = id` を使って、
  -- `g` が単射であることを示す。
  sorry

/- ## 問2: 単射から逆方向の全射
次に `f : A → B` が単射であれば、逆方向の全射 `g : B → A` も存在することを示しましょう。

これも実際にはより強く、`g ∘ f = id` を満たすような `g` が構成できます。一般に、`g ∘ f = id` が成り立つとき、`g` を `f` の左逆写像であるとか、引き込み(retraction)であるとかいいます。

```admonish warning title="注意"
`A` が空の時には関数 `g : B → A` は構成することができないため、`A` が空でないという仮定が必要です。それは `Inhabited A` という引数により表現されています。
```
-/

/-- 単射 `f : A → B` があれば、選択原理を使用することにより
全射 `g : B → A` を作ることができる。 -/
theorem inj_to_surj [Inhabited A] (f : A → B) (hinj : Injective f)
    : ∃ g : B → A, Surjective g := by
  -- まず `g` を構成する。
  -- `g b` の値を構成するために、`b : B` が `f` の像に入っているかで場合分けをし、
  -- 入っていなければ適当な値、入っていれば `b = f a` となる `a` を返すようにする。
  let g : B → A := fun b => sorry

  -- `g` の定義と `f` の単射性から、`g (f a) = a` が成り立つ。
  have gdef : ∀ a, g (f a) = a := by
    sorry

  -- `g ∘ f = id` を使って、
  -- `g` が全射であることを示す。
  sorry
