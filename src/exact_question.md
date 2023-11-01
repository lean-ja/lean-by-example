# exact?

needs: `import Mathlib.Tactic.LibrarySearch`

`exact?` は，ライブラリとローカルコンテキストにある命題を使って，ゴールを閉じることができないか探索します．

```lean
{{#include ../Examples/ExactQuestion.lean:first}}
```

[apply?](./apply_search.md) と似ていますが，`apply?` とは異なりゴールを変形するのではなくて `exact` で直接閉じようとします．

```lean
{{#include ../Examples/ExactQuestion.lean:local}}
```