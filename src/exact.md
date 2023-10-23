# exact

ゴールが `P` で，ローカルコンテキストに `hP: P` があるときに，`exact hP` はゴールを閉じます．

```lean
{{#include ../Examples/Exact.lean:first}}
```

`hP` がゴールの証明になっていないときには，失敗してエラーになります．

`exact ⟨ hP, hQ ⟩` のようにすると，論理積∧の形をした命題を証明することができます．

```lean
{{#include ../Examples/Exact.lean:and}}
```

## assumption との関連

`exact` は常にどの命題を使うか明示する必要がありますが，「ゴールを `exact` で閉じることができるような命題をローカルコンテキストから自動で探す」タクティクもあり，それは [assumption](./assumption.md) です．