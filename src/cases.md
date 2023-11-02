# cases

`cases` は場合分けを行うことができるタクティクです．

たとえば，ローカルコンテキストに `h : P ∨ Q` があるときに `cases h` とすると，仮定に `P` を付け加えたゴール `case inl` と，仮定に `Q` を付け加えたゴール `case inr` を生成します．

補足すると，`inl` と `inr` はそれぞれ `insert left` と `insert right` の略であり，`Or` 型のコンストラクタです．

```lean
{{#include ../Examples/Cases.lean}}
```
