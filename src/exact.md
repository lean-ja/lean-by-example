# exact

ゴールが `P` で，ローカルコンテキストに `hP: P` があるときに，`exact hP` はゴールを閉じます．

```lean
{{#include ../Examples/Exact.lean}}
```

`hP` がゴールの証明になっていないときには，失敗してエラーになります．
