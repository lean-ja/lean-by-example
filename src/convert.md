# convert

ローカルコンテキストに現在のゴールに近いけれども等しくはない `h` があるとき，`exact h` としても失敗します．しかし `convert h` は成功する可能性があり，成功した場合は `h` とゴールの差分を新たなゴールとします．

```lean
{{#include ../Examples/Convert.lean}}
```