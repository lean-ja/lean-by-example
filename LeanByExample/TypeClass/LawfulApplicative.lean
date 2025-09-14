/- # LawfulApplicative

`LawfulApplicative` 型クラスは、[`Applicative`](#{root}/TypeClass/Applicative.md) 型クラスのインスタンスが満たすべき法則を明文化したものです。`LawfulApplicative` クラスのインスタンスになっていることで、「`Applicative` 型クラスのインスタンスは関数適用と整合性があり、計算の文脈を表している」という意味論が適切であることが保証されます。

## 定義

`LawfulApplicative` は、おおむね次のように定義されています。

{{#include ./LawfulApplicative/Def.md}}
-/

/- ## Applicative 則の帰結

`Applicative` のインスタンス `F` は関数適用と整合するという意味論がありますが、`LawfulApplicative` のインスタンスになっているとそれが正しいことが保証されます。
-/

variable {F : Type → Type} [Applicative F] [LawfulApplicative F]
variable {A B C D : Type}

/-- `pure`を介して関数適用と`<*>`が整合している -/
example {x : A} {f : A → B} : pure f <*> (pure x : F A) = pure (f x) := calc
  _ = f <$> pure x := by rw [pure_seq]
  _ = pure (f x) := by rw [map_pure]

example {x : A} {y : B} {f : A → B → C}
    : pure f <*> (pure x : F A) <*> (pure y : F B) = pure (f x y) := by
  simp only [seq_pure, map_pure]
