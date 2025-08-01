import Playground.CS.Ch07.S02.SS04

/- ### 7.2.5 Execution in IMP is Deterministic -/

open BigStep

/-- IMP は決定的 -/
theorem imp_deterministic (S : Stmt) (s t u : State) (ht : (S, s) ==> t) (hu : (S, s) ==> u) : t = u := by
  induction ht generalizing u

  case skip => big_step

  case seq c c' s₁ t₁ _u₁ _hc _hc' ihc ihc' =>
    grind

  case assign v a s =>
    cases hu
    simp

  case if_true B c _c' s t hcond _hc ih =>
    big_step

  case if_false B c _c' s t hcond _hc ih =>
    big_step

  case while_true B c s₁ t₁ _u₁ hcond _hbody _hrest ihc ihw =>
    grind

  case while_false B c s hcond =>
    big_step
