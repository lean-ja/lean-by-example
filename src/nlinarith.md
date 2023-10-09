# nlinarith

needs: `import Mathlib.Tactic.Linarith`

named after: non-linear(非線形) arithmetic(算術)

`nlinarith` は非線形な式も扱えるように `linarith` にいくつか前処理を追加したものです．

```lean
{{#include ../Examples/Nlinarith.lean:first}}
```