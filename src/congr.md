# congr

named after: 合同(congruence)

`congr` は，`⊢ f as = f bs` という形のゴールがあったときに，ゴールを `⊢ as = bs` に変えます．再帰的に適用されるので，`⊢ g (f as) = g (f bs)` という形のゴールでも同じ結果になります．

```lean
{{#include ../Examples/Congr.lean:first}}
```

`congr` が適用される再帰の深さを引数として渡すことができます．これは，主に単に `congr` とするだけだと「行き過ぎ」になるときに調整する目的で使用されます．

```lean
{{#include ../Examples/Congr.lean:option}}
```
