# ring

needs: `import Mathlib.Tactic.Ring`

`ring` は，可換環の等式を示します．

```lean
{{#include ../Examples/Ring.lean:first}}
```

`simp` 等と異なり，`ring?` タクティクは用意されていませんが，`show_term` で具体的にどんなルールが適用されたのかを知ることができます．ただし，その出力結果は非常に長く読みづらいものであることがしばしばです．例えば，

```lean
{{#include ../Examples/Ring.lean:show_term}}
```

の出力をここに掲載すると100行を超えてしまいます．