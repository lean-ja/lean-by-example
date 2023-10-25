# contradiction

矛盾からはどんな命題でも証明することができます．これを爆発律(principle of explosion)と呼びますが，`contradiction` は，この爆発律を使ってゴールを閉じるタクティクです．

ローカルコンテキストに `P` と `¬ P` が同時にあるなど，矛盾した状況にあるときにゴールを閉じます．

```lean
{{#include ../Examples/Contradiction.lean}}
```