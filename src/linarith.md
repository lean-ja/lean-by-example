# linarith

needs: `import Mathlib.Tactic.Linarith`

`linarith` は線形算術(linear arithmetic)からその名前があると考えられるタクティクです．ローカルコンテキストの仮定を読んで，線形な不等式を導くことができます．

```lean
{{#include ../Examples/Linarith.lean:first}}
```