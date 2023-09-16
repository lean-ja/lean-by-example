# apply

ゴールが `⊢ Q` で，ローカルコンテキストに `h: P → Q` があるときに，`apply h` を実行するとゴールが `⊢ P` に書き換わります．

```lean
{{#include ../Examples/Apply.lean:first}}
```

注意点として，`h: P → Q` は `P` の証明を受け取って `Q` の証明を返す関数でもあるので，上記の例は `apply` を使わずに `exact h hP` で閉じることもできます．

```lean
{{#include ../Examples/Apply.lean:exact}}
```

## ¬ について

また，Lean では否定 `¬ P` は `P → False` として実装されているため，ゴールが `⊢ False` であるときに `hn: ¬P` に対して `apply hn` とするとゴールが `⊢ P` に書き換わります．

```lean
{{#include ../Examples/Apply.lean:not}}
```

## exact との関係

`exact` の代わりに `apply` を使うことができます．

```lean
{{#include ../Examples/Apply.lean:alt}}
```
