# linarith

needs: `import Mathlib.Tactic.Linarith`

named after: 線形算術(linear arithmetic)

`linarith` は線形な不等式を導くことができます．

```lean
{{#include ../Examples/Linarith.lean:first}}
```

`linarith` はローカルコンテキストを読み取ってくれるので，`linarith` が通らないとき補題を追加してあげると通るようになることがあります．

```lean
{{#include ../Examples/Linarith.lean:id}}
```
