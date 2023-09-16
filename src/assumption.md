# assumption

`assumption` は，現在のゴール `⊢ P` がローカルコンテキストにあるとき，ゴールを閉じます．

```lean
{{#include ../Examples/Assumption.lean}}
```

## 関連するタクティク

### [exact](./exact.md)

`assumption` による証明は，どの仮定を使うか明示すれば `exact` で書き直すことができます．