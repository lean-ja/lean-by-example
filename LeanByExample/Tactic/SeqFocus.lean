/- # <;>
`<;>` は、直前のタクティクによって生成されたすべてのサブゴールに対して後続のタクティクを適用することを意味するタクティク結合子です。[^name]
-/

variable (P Q : Prop)

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> assumption

/- ## all_goals との違い

`<;>` は [`all_goals`](./AllGoals.md) とよく似た挙動をします。
しかし、`<;>` と `all_goals` は完全に同じではありません。
`<;>` が「直前のタクティクによって生成された全てのサブゴール」に対して後続のタクティクを実行するのに対して、`all_goals` は「すべての未解決のゴール」に対して後続のタクティクまたはタクティクブロックを実行します。

実際に以下のような例ではその違いが現れます。
-/

variable (P Q R : Prop)

/-- <;> を使用したとき -/
example (hP : P) (hQ : Q) (hR : R) : (P ∧ Q) ∧ R := by
  constructor

  constructor <;> try assumption

  -- まだ示すべきことが残っている
  show R
  assumption

/-- all_goals を使用したとき -/
example (hP : P) (hQ : Q) (hR : R) : (P ∧ Q) ∧ R := by
  constructor

  constructor
  all_goals
    try assumption

  -- 証明完了
  done

/- ## ゴールが途中で閉じられたとき

`tac1 <;> tac2` の実行において、`tac1` の実行でゴールが閉じられた場合、`tac2` は実行されずスキップされます。これは `tac1; tac2` とは異なる挙動であることに注意してください。
-/

example (hP : P) : P := by
  -- `assumption`の時点でゴールは閉じているが、エラーにならない
  -- `simp`の実行は単にスキップされる
  assumption <;> simp

example (hP : P) : P := by
  -- `tac1; tac2` では、`tac2` を実行しようとする
  -- そのため `tac2` が実行できないとエラーになることがある
  fail_if_success
    assumption; simp

  assumption

/- [^name]: `<;>` の正式な呼び名はわかりません。`linter.unnecessarySeqFocus` というリンタが存在するので、ここでは `seqFocus` と仮に呼んでいます。-/
