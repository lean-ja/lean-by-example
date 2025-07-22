import Playground.CS.Ch07.S02.SS02

/- ### 7.2.3 Rule Inversion
逆向きの推論ルールを与えることができる。
-/

namespace BigStep

/-- skip に関する BigStep から状態の簡単な式を導く -/
@[grind →, big_step safe destruct]
theorem cases_of_skip {s t : State} : (Stmt.skip, s) ==> t → t = s := by
  grind

/-- skip に関する inversion rule -/
@[simp, grind =]
theorem skip_iff {s t : State} : (Stmt.skip, s) ==> t ↔ t = s := by
  big_step

/-- seq に関する BigStep から状態の簡単な式を導く -/
@[grind →, big_step safe destruct]
theorem cases_of_seq {S T s u} :
    (S;; T, s) ==> u → (∃t, (S, s) ==> t ∧ (T, t) ==> u) := by
  grind

/-- seq に関する inversion rule -/
@[simp, grind =] theorem seq_iff {S T s u} :
    (S;; T, s) ==> u ↔ (∃t, (S, s) ==> t ∧ (T, t) ==> u) := by
  big_step

/-- if に関する BigStep から簡単な条件式を導く (条件式が真の場合) -/
@[grind →, big_step safe destruct]
theorem cases_if_of_true {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
  grind

/-- if に関する BigStep から簡単な条件式を導く (条件式が偽の場合) -/
@[grind →, big_step safe destruct]
theorem cases_if_of_false {B S T s t} (hcond : ¬ B s) : (ifThenElse B S T, s) ==> t → (T, s) ==> t := by
  grind

/-- ifThenElse の分解時に現れる式を分解するための命題論理の補題 -/
@[big_step unsafe 30% apply]
theorem and_excluded {P Q R : Prop} (hQ : P → Q) (hR : ¬ P → R) : (P ∧ Q ∨ ¬ P ∧ R) := by
  grind

/-- if に関する inversion rule -/
@[simp] theorem if_iff {B S T s t} : (ifThenElse B S T, s) ==> t ↔
    (B s ∧ (S, s) ==> t) ∨ (¬ B s ∧ (T, s) ==> t) := by
  big_step

/-- while の BigStep が仮定にあるときに簡単な状態の式を導く(条件式が偽のとき) -/
@[grind →, big_step safe destruct]
theorem cases_while_of_false {B S s t} (hcond : ¬ B s) : (whileDo B S, s) ==> t → s = t := by
  grind

/-- while の BigStep が仮定にあるときに簡単な状態の式を導く(条件式が真のとき) -/
@[grind →, big_step unsafe 20% apply]
theorem cases_while_of_true {B S s u} (hcond : B s) : (whileDo B S, s) ==> u →
    (∃ t, (S, s) ==> t ∧ (whileDo B S, t) ==> u) := by
  grind

/-- while に関する inversion rule。
条件式が真か偽かで場合分けをする -/
@[grind =]
theorem while_iff {B S s u} : (whileDo B S, s) ==> u ↔
    (∃ t, B s ∧ (S, s) ==> t ∧ (whileDo B S, t) ==> u) ∨ (¬ B s ∧ u = s) := by
  big_step

/-- while の条件式が真のときの inversion rule -/
@[grind =>]
theorem while_true_iff {B S s u} (hcond : B s) : (whileDo B S, s) ==> u ↔
    (∃ t, (S, s) ==> t ∧ (whileDo B S, t) ==> u) := by
  big_step

/-- while の条件式が偽のときの inversion rule -/
@[simp, grind =>]
theorem while_false_iff {B S s t} (hcond : ¬ B s) : (whileDo B S, s) ==> t ↔ t = s := by
  big_step

/- inversion rule を使って次のような命題が証明できる -/

example (c₁ c₂ : Stmt) (s₁ s₃ : State) : (c₁;; c₂, s₁) ==> s₃ →
    ∃s₂, (c₁, s₁) ==> s₂ ∧ (c₂, s₂) ==> s₃ := by
  big_step

/-- seq `;;` を左結合にしても右結合にしても意味論の観点からは変化がない。 -/
@[grind _=_]
theorem seq_assoc (c₁ c₂ c₃ : Stmt) (s u : State) :
    ((c₁;; c₂);; c₃, s) ==> u ↔ (c₁;; (c₂;; c₃), s) ==> u := by
  big_step

end BigStep
