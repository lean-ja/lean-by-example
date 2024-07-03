/- # termination_by
`termination_by` は，再帰関数が有限回の再帰で停止することを Lean にわかってもらうための構文で，「再帰のたびに減少する指標」を指定します．
-/
namespace TerminationBy --#
-- 何も指定しないと，停止することが Lean にはわからないのでエラーになる
/--
error: fail to show termination for
  TerminationBy.M
with errors
structural recursion cannot be used:

argument #1 cannot be used for structural recursion
  failed to eliminate recursive application
    M (n + 11)

failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬n > 100
⊢ n + 11 < n
-/
#guard_msgs in
/-- McCarthy の 91 関数 -/
def M (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    M (M (n + 11))

/- 以下のように，`termination_by` で「再帰適用で減少していくもの」を指定することができ，うまくいけばエラーがなくなります．-/

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
        n - 10 ≤ (n + 11) - 10 - 10 := by omega
        _ ≤ (M (n + 11)) - 10 := by omega
        _ ≤ M (M (n + 11)) := (M (M (n + 11)).val).property
      ⟨M (M (n + 11)), lem⟩
  termination_by 101 - n

end TerminationBy --#
