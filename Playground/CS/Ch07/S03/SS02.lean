import Playground.CS.Ch07.S03.SS01

/--
`final (S, s)` は `(S, s)` がこれ以上評価を進めることができないことを表す.
IMPでは `S = skip` に限られるが, より複雑な言語では `1 + true` のような例がある.
-/
def final (S : Stmt) (s : State) : Prop :=
  ¬ ∃ S' s', (S, s) ⇒ (S', s')

@[simp]
theorem skip_is_final (s : State) : final skip s := by
  intro h
  obtain ⟨S', s', h⟩ := h
  -- `h` はあり得ない
  contradiction

/-- `skip` 以外のコマンドは `final` ではない。記述を簡略化したバージョン -/
theorem not_final_of_ne_skip {S : Stmt} (h : S ≠ skip) (s : State) : ∃ S' s', (S, s) ⇒ (S', s') := by
  induction S
  case skip => contradiction
  case assign v a =>
    clear h
    refine ⟨skip, s[v ↦ a s], ?_⟩
    apply SmallStep.assign
  case seq S₁ S₂ ih₁ ih₂ =>
    clear h
    by_cases if_skip : S₁ = skip
    case pos =>
      rw [if_skip]
      refine ⟨S₂, s, ?_⟩
      small_step
    case neg => small_step
  case ifThenElse B S₁ S₂ ih₁ ih₂ =>
    clear h
    by_cases h : B s
    · small_step
    · small_step
  case whileDo B S ih =>
    clear h
    small_step

/-- `skip` 以外のコマンドは `final` ではない

**TODO**: なぜかこれを `simp` 補題にしても、次の 7.17 の証明で自動で使われない。原因は何か？
-/
theorem skip_of_final {S : Stmt} {s : State} (h : final S s) : S = skip := by
  by_cases if_skip : S = skip
  case pos => assumption
  case neg =>
    have := not_final_of_ne_skip if_skip s
    aesop

add_small_step_rules safe destruct [skip_of_final]

/-- ### Lemma 7.17
`final` が成り立つことと、コマンドが `skip` であることは同値。
-/
@[simp] theorem skip_iff_final (S : Stmt) (s : State) : final S s ↔ (S = skip) := by
  constructor <;> intro h
  case mp => small_step
  case mpr => simp_all

/-- ### Lemma 7.18
BigStep と SmallStep の関係を表す命題を final で書き換えたもの
-/
theorem big_step_iff_final (S : Stmt) (s : State) :
    (∃ t, (S, s) ==> t) ↔ (∃ S' s', (S, s) ⇒* (S', s') ∧ final S' s') := by
  simp [skip_iff_final, big_step_iff_small_step_star]
