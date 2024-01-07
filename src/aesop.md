# aesop

`aesop` は，Automated Extensible Search for Obvious Proofs (自明な証明の拡張可能な自動探索)からその名があるタクティクです．Isabell の `auto` と似ています．`aesop` は `intro` や `simp` を使用してルーチンな証明を自動で行ってくれます．

また `aesop?` を使うことにより，ゴールを閉じるのにどのようなタクティクが用いられたか確認することが可能です．

より詳細には下記のような性質を持ちます:

* `simp` と同様に，`@[aesop]` というタグを付けることで補題や定義を登録し，`aesop` に使用させることができます．
* `aesop` は登録されたルールを最初のゴールに適用しようとします．成功してサブゴールが生成されたら，`aesop` はサブゴールにも再帰的にルールを適用し，探索ツリーを構築します．
* 探索ツリーは最良優先探索(best-first search)により探索されます．ルールには有用である可能性が高いか低いかもマークすることができ，`aesop` は探索ツリー内のより有望そうなゴールを先に調べます．
* `aesop` はまず `simp_all` を用いてゴールを正規化するため，`simp` が使用する補題は `aesop` にも使用されます．

もっと詳しいことが知りたい方は，[aesopのリポジトリ](https://github.com/leanprover-community/aesop)をご参照ください．

```lean
{{#include ../Examples/Aesop.lean}}
```
