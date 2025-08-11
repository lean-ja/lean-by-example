/- # LawfulApplicative

`LawfulApplicative` 型クラスは、[`Applicative`](#{root}/TypeClass/Applicative.md) 型クラスのインスタンスが満たすべき法則を明文化したものです。`LawfulApplicative` クラスのインスタンスになっていることで、「`Applicative` 型クラスは、関数適用の一般化であり、計算効果をエンコードしている」という意味論が適切であることが保証されます。

## 定義

`LawfulApplicative` は、おおむね次のように定義されています。

{{#include ./LawfulApplicative/Def.md}}
-/
