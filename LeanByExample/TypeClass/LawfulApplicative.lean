/- # LawfulApplicative

`LawfulApplicative` 型クラスは、[`Applicative`](#{root}/TypeClass/Applicative.md) 型クラスのインスタンスが満たすべき法則を明文化したものです。`LawfulApplicative` クラスのインスタンスになっていることで、「`Applicative` 型クラスは、関数適用の一般化であり、計算効果をエンコードしている」という意味論が適切であることが保証されます。

## 定義

`LawfulApplicative` は、おおむね次のように定義されています。

{{#include ./LawfulApplicative/Def.md}}
-/

/- ## Applicative 則の帰結 -/

variable {F : Type → Type} [Applicative F] [LawfulApplicative F]
variable {A B C D : Type}

/-- `pure`を介して関数適用と`<*>`が整合している -/
example {x : A} {f : A → B} : pure f <*> (pure x : F A) = pure (f x) := calc
  _ = f <$> pure x := by rw [pure_seq]
  _ = pure (f x) := by rw [map_pure]
