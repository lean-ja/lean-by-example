import Playground.CS.Ch07.S02.SS02

/- ### 7.2.3 Rule Inversion
逆向きの推論ルールを与えることができる。
-/

namespace BigStep

/-- skip に関する BigStep から状態の簡単な式を導く -/
theorem cases_of_skip {s t : State} : (Stmt.skip, s) ==> t → t = s := by
  intro h
  cases h
  rfl

-- skip に関する BigStep が仮定にあるときに big_step で扱えるようにする
add_big_step_rules safe destruct [cases_of_skip]

/-- skip に関する inversion rule -/
@[simp] theorem skip_iff {s t : State} : (Stmt.skip, s) ==> t ↔ t = s := by
  big_step

/-- seq に関する BigStep から状態の簡単な式を導く -/
theorem cases_of_seq {S T s u} :
    (S;; T, s) ==> u → (∃t, (S, s) ==> t ∧ (T, t) ==> u) := by
  intro h
  cases h
  big_step

-- seq に関する BigStep が仮定にあるときに big_step で扱えるようにする
add_big_step_rules safe destruct [cases_of_seq]

/-- seq に関する inversion rule -/
@[simp] theorem seq_iff {S T s u} :
    (S;; T, s) ==> u ↔ (∃t, (S, s) ==> t ∧ (T, t) ==> u) := by
  big_step

/-- if に関する BigStep から簡単な条件式を導く (条件式が真の場合) -/
theorem cases_if_of_true {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
  intro h
  cases h <;> try contradiction
  assumption

/-- if に関する BigStep から簡単な条件式を導く (条件式が偽の場合) -/
theorem cases_if_of_false {B S T s t} (hcond : ¬ B s) : (ifThenElse B S T, s) ==> t → (T, s) ==> t := by
  intro h
  cases h <;> try contradiction
  assumption

-- if に関する BigStep が仮定にあるときに big_step で扱えるようにする
add_big_step_rules safe destruct [cases_if_of_true]
add_big_step_rules safe destruct [cases_if_of_false]

/-- ifThenElse の分解時に現れる式を分解するための命題論理の補題 -/
theorem and_excluded {P Q R : Prop} (hQ : P → Q) (hR : ¬ P → R) : (P ∧ Q ∨ ¬ P ∧ R) := by
  by_cases h : P
  · left
    exact ⟨h, hQ h⟩
  · right
    exact ⟨h, hR h⟩

add_big_step_rules unsafe 30% apply [and_excluded]

/-- if に関する inversion rule -/
@[simp] theorem if_iff {B S T s t} : (ifThenElse B S T, s) ==> t ↔
    (B s ∧ (S, s) ==> t) ∨ (¬ B s ∧ (T, s) ==> t) := by
  big_step

/-- while の BigStep が仮定にあるときに簡単な状態の式を導く(条件式が偽のとき) -/
theorem cases_while_of_false {B S s t} (hcond : ¬ B s) : (whileDo B S, s) ==> t → s = t := by
  intro h
  rcases h with h | h
  · simp_all
  · rfl

add_big_step_rules safe [destruct cases_while_of_false (rule_sets := [BigStepRules])]

/-- while の BigStep が仮定にあるときに簡単な状態の式を導く(条件式が真のとき) -/
theorem cases_while_of_true {B S s u} (hcond : B s) : (whileDo B S, s) ==> u →
    (∃ t, (S, s) ==> t ∧ (whileDo B S, t) ==> u) := by
  intro h
  cases h
  · aesop
  · simp_all

-- 再帰的に while 文が出てくるので、unsafe ルールとして登録する
add_big_step_rules unsafe 20% [apply cases_while_of_true (rule_sets := [BigStepRules])]

/-- while に関する inversion rule。
条件式が真か偽かで場合分けをする -/
theorem while_iff {B S s u} : (whileDo B S, s) ==> u ↔
    (∃ t, B s ∧ (S, s) ==> t ∧ (whileDo B S, t) ==> u) ∨ (¬ B s ∧ u = s) := by
  big_step

/-- while の条件式が真のときの inversion rule -/
theorem while_true_iff {B S s u} (hcond : B s) : (whileDo B S, s) ==> u ↔
    (∃ t, (S, s) ==> t ∧ (whileDo B S, t) ==> u) := by
  big_step

/-- while の条件式が偽のときの inversion rule -/
@[simp] theorem while_false_iff {B S s t} (hcond : ¬ B s) : (whileDo B S, s) ==> t ↔ t = s := by
  big_step

/- inversion rule を使って次のような命題が証明できる -/

example (c₁ c₂ : Stmt) (s₁ s₃ : State) : (c₁;; c₂, s₁) ==> s₃ →
    ∃s₂, (c₁, s₁) ==> s₂ ∧ (c₂, s₂) ==> s₃ := by
  big_step

/-- seq `;;` を左結合にしても右結合にしても意味論の観点からは変化がない。 -/
theorem seq_assoc (c₁ c₂ c₃ : Stmt) (s u : State) :
    ((c₁;; c₂);; c₃, s) ==> u ↔ (c₁;; (c₂;; c₃), s) ==> u := by
  big_step

end BigStep
