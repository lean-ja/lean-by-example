# suffices

`suffices` は，数学でよくある「～を示せば十分である」という推論を行うタクティクです．

ゴールが `⊢ P` であるときに `suffices Q from` を実行すると，

* `suffices Q from` のブロック内では，仮定に `this: Q` が追加され，
* `suffices Q from` 以降では，ゴールが `⊢ Q` に書き換えられます．

`apply` と似ていますが，`apply` と違って「十分条件になっていること」の証明が明らかでないときにも使うことができます．

`suffices Q from ...` という形式の場合は，証明を直接構成することが必要です．`suffices Q from by ...` とすると，タクティクによって証明を構成するモードになります．

```lean
{{#include ../Examples/Suffices.lean}}
```
