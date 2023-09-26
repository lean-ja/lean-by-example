# push_neg

needs: `import Mathlib.Tactic.PushNeg`

named after: 押し込む(push) 否定(negation)

`push_neg` はドモルガン則を使って，否定を式の中に押し込みます．たとえば

* `¬ (P ∧ Q)` は `P → ¬ Q` に，

* `¬ ∀ x, P x` は `∃ x, ¬ P x` に

という調子で変形します．[^impl]

```lean
{{#include ../Examples/PushNeg.lean:first}}
```

```lean
{{#include ../Examples/PushNeg.lean:all_exists}}
```

[^impl] モードによって `¬ (P ∧ Q)` を `P → ¬ Q` としたり，`¬ P ∨ ¬ Q` としたりします．