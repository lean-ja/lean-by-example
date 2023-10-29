# tauto

needs: `import Mathlib.Tactic.Tauto`

named after: トートロジー(tautology)

`tauto` は， トートロジー(恒真式)であることに基づいてゴールを閉じるタクティクです． ゴールを閉じることができなければエラーになります．

```lean
{{#include ../Examples/Tauto.lean:first}}
```
