# ext

数学では集合 `A, B ⊂ α` について `A = B` を示すときに `x ∈ A` と `x ∈ B` が同値であることを示すのが常套手段として行われますが，`ext` はそういうことを行うタクティクです．

Mathlib4 に依存しているタクティクです．

```lean
{{#include ../Examples/Mathlib/Ext.lean:first}}
```

なお `A ⊂ B` を示すために元を取るのは `intro x` で可能です．
