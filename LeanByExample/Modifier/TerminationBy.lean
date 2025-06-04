/- # termination_by
`termination_by` 句(termination_by clause)は、再帰関数が有限回の再帰で停止することを Lean にわかってもらうために、「再帰のたびに減少する指標」を指定します。
-/
-- 何も指定しないと、停止することが Lean にはわからないのでエラーになる
/-⋆-//--
error: fail to show termination for
  M
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    M (n + 11)


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n #1
1) 32:7-17 ?  ≤
2) 32:4-18 _  ?

#1: 100 - n

Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in --#
/-- McCarthy の 91 関数 -/
def M (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    M (M (n + 11))

/- 以下のように、`termination_by` で「再帰適用で減少していくもの」を指定することができ、うまくいけばエラーがなくなります。-/

/-- McCarthy の 91 関数 -/
def Mc91 (n : Nat) : Nat :=
  (M n).val
where
  M (n : Nat) : { m : Nat // m ≥ n - 10 } :=
    if h : n > 100 then
      ⟨n - 10, by omega⟩
    else
      have : n + 11 - 10 ≤ M (n + 11) := (M (n + 11)).property
      have lem : n - 10 ≤ M (M (n + 11)) := calc
        _ ≤ (n + 11) - 10 - 10 := by omega
        _ ≤ (M (n + 11)) - 10 := by omega
        _ ≤ M (M (n + 11)) := (M (M (n + 11)).val).property

      ⟨M (M (n + 11)), lem⟩
  termination_by 101 - n
