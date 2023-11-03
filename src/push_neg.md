# push_neg

`push_neg` はドモルガン則を使って，否定(negation)を式の中に押し込みます．デフォルトの設定だと, たとえば

* `¬ (P ∧ Q)` は `P → ¬ Q` に，

* `¬ ∀ x, P x` は `∃ x, ¬ P x` に

という調子で変形します．

```lean
{{#include ../Examples/PushNeg.lean}}
```
