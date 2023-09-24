# rw

`rw` は rewrite（書き換え）を行うタクティクです．等式や同値をもとに書き換えを行います．

`hab: a = b` や `hPQ : P ↔ Q` がローカルコンテキストにあるとき，

* `rw [hab]` はゴールの中の `a` をすべて `b` に置き換え，
* `rw [hPQ]` はゴールの中の `P` をすべて `Q` に置き換えます．

順番は重要で，`b` を `a` に置き換えたいときなどは `rw [← hab]` のように `←` をつけます．

`h1, h2, ...` について続けて置き換えを行いたいときは，`rw [h1, h2, ...]` のようにします．

ゴールではなく，ローカルコンテキストにある `h: P` を書き換えたいときには `at` をつけて `rw [hPQ] at h` とします．すべての箇所で置き換えたいときは `rw [hPQ] at *` とします．

```lean
{{#include ../Examples/Rw.lean:rw}}
```

## nth_rewrite

`nth_rewrite`は特定の項のみを書き換えるタクティクです．

項の指定は対象の式中に現れる順番を1始まりで指定します．
指定された順番が式中の対象の項の数よりも多い場合はエラーになります．

```lean
{{#include ../Examples/Rw.lean:nth_rewrite_import}}
{{#include ../Examples/Rw.lean:nth_rewrite}}
```
