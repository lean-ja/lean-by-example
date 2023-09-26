# linarith

needs: `import Mathlib.Tactic.Linarith`

named after: 線形算術(linear arithmetic)

`linarith` は線形な(不)等式を導くことができます．

```lean
{{#include ../Examples/Linarith.lean:first}}
```

`linarith` はローカルコンテキストを読み取ってくれるので，`linarith` が通らないとき補題を追加してあげると通るようになることがあります．

```lean
{{#include ../Examples/Linarith.lean:id}}
```

## 補足

もう少し詳細に書くと，`linarith` は「ロールコンテキストにある線形な(不)等式系に矛盾があるか調べる」タクティクなので，次のような使い方もできます．

```lean
{{#include ../Examples/Linarith.lean:general}}
```