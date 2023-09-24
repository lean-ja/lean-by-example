# choose

needs: `import Mathlib.Tactic.Choose`

`h : ∀ x, ∃ y, P(x, y)` が成り立っているときに，`choose f hf using h` は写像 `f: X → Y` と `f` が満たす性質 `hf : ∀ x, P(x, f x)` のペアを作ります．

```lean
{{#include ../Examples/Choose.lean:first}}
```