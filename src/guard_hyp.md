# guard_hyp

needs: `import Std.Tactic.GuardExpr`

`guard_hyp` は，ローカルコンテキストにある命題を確認するタクティクです．指定した仮定が存在すれば成功し，そうでなければ失敗します．

```lean
{{#include ../Examples/GuardHyp.lean:first}}
```

通常の証明で使うことはあまりないかもしれません．このタクティクリストでは，ローカルコンテキストの変化を説明するために使用することがあります．