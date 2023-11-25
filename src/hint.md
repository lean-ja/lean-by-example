# hint

`hint` は複数のタクティクの中から提案を出してくれるタクティクです．デフォルトでは

* [split](./split.md)
* [intro](./intro.md)
* [aesop](./aesop.md)
* `decide`
* [exact?](./exact_question.md)
* `simp_all?`
* [linarith](./linarith.md)

の7つのタクティクを同時に試します．

* ゴールを閉じることに成功したものは緑色で示され，
* 進捗があったものはウィジェットに新しいゴールを示します．

登録されているタクティクに `tac` を追加するには，`register_hint tac` を実行します．

```lean
{{#include ../Examples/Hint.lean}}
```