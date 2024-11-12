/- # linter.style.multiGoal

`linter.style.multiGoal` は、よくない証明の書き方を指摘するリンターの一つです。

Lean では、複数のサブゴールがあるときにタクティクを実行すると最初のゴールに対して実行されるのですが、証明を構造化するという観点からは、ゴールの一つにフォーカスする（infoview に一つしかゴールが表示されないようにする）べきです。
このリンタはそのような問題を指摘します。
-/
import Mathlib.Tactic.Linter.Multigoal

set_option linter.style.multiGoal true

/--
warning: There are 2 unclosed goals before 'exact hP' and at least one remaining goal afterwards.
Please focus on the current goal, for instance using `·` (typed as "\.").
note: this linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
  example {P Q : Prop} (hP : P) (hQ : Q) : P ∧ Q := by
    -- ゴールが２つ生成される
    constructor

    -- この時点でサブゴールが２つあるのに、
    -- フォーカスせずにタクティクを実行しているので警告が出る
    exact hP
    exact hQ

-- 良い証明の例
example {P Q : Prop} (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ
