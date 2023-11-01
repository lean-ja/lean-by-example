# by_cases

`by_cases` は排中律を使って場合分けをするタクティクです．

`by_cases h: P` とすると，`P` が成り立つときと成り立たないときのゴールがそれぞれ生成されます．

```lean
{{#include ../Examples/ByCases.lean}}
```