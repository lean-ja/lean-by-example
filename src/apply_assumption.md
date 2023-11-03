# apply_assumption

`apply_assumption` は，ゴールが `⊢ head` であるときに，`... → ∀ _, ... → head` という形の命題をローカルコンテキストから探し，それを用いてゴールを書き換えます．

```lean
{{#include ../Examples/ApplyAssumption.lean}}
```
