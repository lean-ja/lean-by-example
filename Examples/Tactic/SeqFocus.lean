/- # <;>
`<;>` (seq focus)は、直前のタクティクによって生成されたすべてのサブゴールに対して後続のタクティクを適用することを意味するタクティク結合子です。
-/

variable (P Q : Prop)

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> assumption

/- これは [`all_goals`](./AllGoals.md) とよく似た挙動です。

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
