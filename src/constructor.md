# constructor

ゴールが `⊢ P ∧ Q` であるとき，`constructor` を実行すると，ゴールが２つのゴール `⊢ P` と `⊢ Q` に分割されます．

```lean
{{#include ../Examples/Constructor.lean:first}}
```

## 同値を示す

`constructor` はゴールが `⊢ P ↔ Q` であるときにも使用できます．

```lean
{{#include ../Examples/Constructor.lean:iff}}
```