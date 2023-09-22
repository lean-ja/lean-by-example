# by_contra

needs: `import Mathlib.Tactic.ByContra`

`by_contra` は，背理法を使いたいときに役立つタクティクです．

ゴールが `⊢ P` であるときに `by_contra h` を実行すると，`h : ¬ P` がローカルコンテキストに追加されて，同時にゴールが `⊢ False` になります．

```lean
{{#include ../Examples/ByContra.lean:first}}
```
