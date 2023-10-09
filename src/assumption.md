# assumption

`assumption` は，現在のゴール `⊢ P` がローカルコンテキストにあるとき，ゴールを閉じます．

```lean
{{#include ../Examples/Assumption.lean}}
```

## exact との関連

`assumption` による証明は，どの仮定を使うか明示すれば [exact](./exact.md) で書き直すことができます．