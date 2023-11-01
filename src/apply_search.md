# apply?

`apply?` は，カレントゴールを `apply` や [refine](./refine.md) で変形することができないか，ライブラリから検索して提案してくれるタクティクです．

複数の候補が提案されたときは，どれを選ぶとゴールが何に変わるのか表示されるので，その中から好ましいものを選ぶと良いでしょう．

```lean
{{#include ../Examples/ApplySearch.lean}}
```
