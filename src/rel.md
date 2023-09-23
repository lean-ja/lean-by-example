# rel

needs: `import Mathlib.Tactic.GCongr`

named after: 関係(relation)

`rel` は，不等式を代入して適用し，不等式を示します．

```lean
{{#include ../Examples/Rel.lean:first}}
```

`rel` は，たとえば整数 `x: Int` に対して `0 ≤ x ^ 2` であることを自動的に適用するなど, 多少の推論を行います．

```lean
{{#include ../Examples/Rel.lean:guess}}
```
