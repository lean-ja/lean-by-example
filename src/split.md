# split

ゴールにある `if ... then ... else` 式を扱うのに有用なタクティクです．

if 式を扱う必要が生じるのは，典型的には Lean で定義したアルゴリズムや関数に関して，何か性質を証明しようとしたときです．

```lean
{{#include ../Examples/Split.lean:first}}
```