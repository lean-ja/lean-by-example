# apply?

needs: `import Mathlib.Tactic.LibrarySearch`

`apply?` は，ゴールを閉じるのに必要な命題をライブラリから検索してきて，提案してくれるタクティクです．

```lean
{{#include ../Examples/ApplyQuestion.lean:first}}
```

複数の候補が提案されたときは，どれを選ぶとゴールが何に変わるのか表示されるので，その中から好ましいものを選ぶと良いでしょう．