# by_contra

`by_contra` は，背理法を使いたいときに役立つタクティクです．`Mathlib.Tactic.ByContra` に依存しています．

ゴールが `⊢ P` であるときに `by_contra h` を実行すると，`h : ¬ P` がローカルコンテキストに追加されて，同時にゴールが `⊢ False` になります．

```lean
{{#include ../Examples/ByContra.lean:first}}
```
