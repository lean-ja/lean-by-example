# aesop

`aesop` は，`intro` や `simp` を使用してルーチンな証明を自動で行おうとします．`Aesop` ライブラリに依存しています．

```lean
{{#include ../Examples/Aesop.lean:first}}
```

## aesop?

`aesop` が成功したとき，`aesop?` に置き換えると，ゴールを達成するのにどんなタクティクを使用したか教えてくれます．

```lean
{{#include ../Examples/Aesop.lean:question}}
```