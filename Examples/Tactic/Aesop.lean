/-
# aesop

`aesop` は，Automated Extensible Search for Obvious Proofs (自明な証明の拡張可能な自動探索)からその名があるタクティクです．Isabell の `auto` と似ています．`aesop` は `intro` や `simp` を使用してルーチンな証明を自動で行ってくれます．
-/
import Aesop -- `aesop` を使用するため
import Mathlib.Init.Function -- `Injective` を使用するため

-- 以下 `X` `Y` `Z`を集合とする
variable {X Y Z : Type}

open Function

-- 合成 `g ∘ f` が単射なら，`f` も単射
example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  show ∀ ⦃a₁ a₂ : X⦄, f a₁ = f a₂ → a₁ = a₂

  -- 示すべきことがまだまだあるように見えるが，一発で証明が終わる
  aesop

/-!
## aesop?

`aesop` が成功するとき，`aesop?` に置き換えるとゴールを達成するのにどんなタクティクを使用したか教えてくれます．
-/

example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]

  /-
  Try this:
  intro a₁ a₂ a
  apply hgfinj
  simp_all only [comp_apply]
  -/
  aesop?

/-! ## 補足
より詳細には `aesop` は下記のような性質を持ちます:

* `simp` と同様に，`@[aesop]` という属性(attribute)を付けることで補題や定義を登録し，`aesop` に使用させることができます．
* `aesop` は登録されたルールを最初のゴールに適用しようとします．成功してサブゴールが生成されたら，`aesop` はサブゴールにも再帰的にルールを適用し，探索ツリーを構築します．
* 探索ツリーは最良優先探索(best-first search)により探索されます．ルールには有用である可能性が高いか低いかもマークすることができ，`aesop` は探索ツリー内のより有望そうなゴールを先に調べます．
* `aesop` はまず `simp_all` を用いてゴールを正規化するため，`simp` が使用する補題は `aesop` にも使用されます．

もっと詳しいことが知りたい方は，[aesopのリポジトリ](https://github.com/leanprover-community/aesop)をご参照ください．

[Test](hoge.md)
-/
