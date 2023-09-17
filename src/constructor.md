# constructor

ゴールが `⊢ P ∧ Q` であるとき，`constructor` を実行すると，ゴールが２つのゴール `⊢ P` と `⊢ Q` に分割されます．

```lean
{{#include ../Examples/Constructor.lean:first}}
```

なお `h: P ∧ Q` から `P` や `Q` の証明を得るのは，それぞれ `h.left` と `h.right` で可能です．

```lean
{{#include ../Examples/Constructor.lean:split}}
```

## 同値を示す

`constructor` はゴールが `⊢ P ↔ Q` であるときにも使用できます．

```lean
{{#include ../Examples/Constructor.lean:iff}}
```