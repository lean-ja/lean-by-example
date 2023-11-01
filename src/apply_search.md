# apply?

needs: `import Mathlib.Tactic.LibrarySearch`

`apply?` は，ゴールを閉じるのに必要な命題をライブラリから検索してきて，提案してくれるタクティクです．

```lean
{{#include ../Examples/ApplySearch.lean:first}}
```

複数の候補が提案されたときは，どれを選ぶとゴールが何に変わるのか表示されるので，その中から好ましいものを選ぶと良いでしょう．

## 補足

`apply?` はあくまで証明を書くときに補助として使うものです．`sorry` と同じように，清書した証明に残してはいけません．

`sorry` と同じと言いましたが，実際 `apply?` は sorryAx [^sorry] を裏で使用します．これは，`#explode` で証明の中身を出力させれば分かります．`sorry` を使っているという旨の警告も出ます．

```lean
{{#include ../Examples/ApplySearch.lean:sorry}}
```

[^sorry] `sorry` が裏で使用している公理のこと