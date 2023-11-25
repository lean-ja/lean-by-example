# unfold

`unfold` は，式の展開(unfolding)を行うタクティクです．定義に基づいて式を展開します．

何も指定しなければゴールを変形しようとします．ローカルコンテキストにある項 `h` について展開を行うには，`unfold ... at h` のように `at` を付けます．

[simp](./simp.md) の派生である `dsimp` タクティクを使っても同様のことができます．

```lean
{{#include ../Examples/Unfold.lean}}
```