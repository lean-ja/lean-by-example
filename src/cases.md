# cases

`cases` は場合分けを行います．ローカルコンテキストに `h: P ∨ Q` があるときに `cases h` とすると，仮定に `P` を付け加えたゴール `inl` と，仮定に `Q` を付け加えたゴール `inr` を生成します．それぞれ，`insert left` と `insert right` の略ではないかと思います．

```lean
{{#include ../Examples/Cases.lean:first}}
```

## case を書かない

上記の例では `case` を場合分けの枝ごとに書いていますが，下の例のように `case` を書かずに済ませることもできます．

```lean
{{#include ../Examples/Cases.lean:no_case}}
```

## cases'

`Mathlib.Tactic.Cases` に依存したタクティクですが，`cases'` を使用すると分解した仮定に簡潔に名前をつけることができます．

```lean
{{#include ../Examples/Cases.lean:dash}}
```
