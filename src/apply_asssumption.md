# apply_assumption

needs: `import Mathlib.Tactic.SolveByElim`

`apply_assumption` は，ゴールが `⊢ head` であるときに，`... → ∀ _, ... → head` という形の命題をローカルコンテキストから探し，それを用いてゴールを書き換えます．

```lean
{{#include ../Examples/ApplyAssumption.lean:first}}
```

タクティクを繰り返すことを指示するタクティク `repeat` と組み合わせると，「ローカルコンテキストにある仮定を適切に選んで `apply`, `exact` することを繰り返し，ゴールを閉じる」ことができます．

```lean
{{#include ../Examples/ApplyAssumption.lean:repeat}}
```