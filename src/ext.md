# ext

数学では集合 `A, B ⊂ α` について `A = B` を示すときに `x ∈ A` と `x ∈ B` が同値であることを示すのが常套手段として行われますが，`ext` はそういうことを行うタクティクです．

`Std.Tactic.Ext` に依存しているタクティクです．`@[ext]` で登録されたルールを使用するため，集合の等式 `A = B` を示すときは `Mathlib.Data.SetLike.Basic` も必要です．

```lean
{{#include ../Examples/Mathlib/Ext.lean:first}}
```

なお `A ⊂ B` を示すために元を取るのは `intro x` で可能です．
