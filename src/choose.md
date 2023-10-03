# choose

needs: `import Mathlib.Tactic.Choose`

`h : ∀ x, ∃ y, P(x, y)` が成り立っているときに，`choose f hf using h` は写像 `f: X → Y` と `f` が満たす性質 `hf : ∀ x, P(x, f x)` のペアを作ります．

```lean
{{#include ../Examples/Choose.lean:first}}
```

## 補足

`choose` が自動で示してくれることは選択公理 `Classical.choice` を使って手動で示すことができます．たとえば次のようになります．

```lean
{{#include ../Examples/Choose.lean:no_choose}}
```