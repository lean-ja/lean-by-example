# rel

needs: `import Mathlib.Tactic.GCongr`

`rel` は，不等式を代入して適用し，不等式を示します．関係(relation)を示すことからその名前があるようです．

```lean
{{#include ../Examples/Rel.lean:first}}
```

`rel` は，たとえば整数 `x: Int` に対して `0 ≤ x ^ 2` であることを自動的に適用するなど, 多少の推論を行います．

```lean
{{#include ../Examples/Rel.lean:guess}}
```
