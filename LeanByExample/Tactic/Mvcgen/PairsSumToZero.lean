import Std.Data.HashSet.Lemmas
import Std.Tactic.Do

open Std Do

variable {α : Type}

def List.Any₂ (P : α → α → Prop) (l : List α) : Prop := ¬ l.Pairwise (fun x y => ¬P x y)

theorem List.any₂_iff_not_pairwise {P : α → α → Prop} {l : List α} :
    l.Any₂ P ↔ ¬l.Pairwise (fun x y => ¬P x y) := by
  grind [List.Any₂]

@[simp, grind ·]
theorem not_any₂_nil {P : α → α → Prop} : ¬List.Any₂ P [] := by
  simp [List.any₂_iff_not_pairwise]

@[simp, grind =]
theorem List.any₂_cons {P : α → α → Prop} {x : α} {xs : List α} :
    List.Any₂ P (x :: xs) ↔ (∃ y ∈ xs, P x y) ∨ List.Any₂ P xs := by
  grind [List.any₂_iff_not_pairwise, pairwise_cons]

@[simp, grind =]
theorem List.any₂_append {P : α → α → Prop} {xs ys : List α} :
    List.Any₂ P (xs ++ ys) ↔ List.Any₂ P xs ∨ List.Any₂ P ys ∨ (∃ x ∈ xs, ∃ y ∈ ys, P x y) := by
  grind [List.any₂_iff_not_pairwise]


def pairsSumToZero (l : List Int) : Bool := Id.run do
  let mut seen : HashSet Int := ∅
  for x in l do
    if -x ∈ seen then
      return true
    seen := seen.insert x
  return false

set_option mvcgen.warning false

theorem pairsSumToZero_spec (l : List Int) :
    pairsSumToZero l = true ↔ l.Any₂ (fun a b => a + b = 0) := by
  generalize h : pairsSumToZero l = r
  apply Id.of_wp_run_eq h

  mvcgen invariants
  · Invariant.withEarlyReturn
    (onReturn := fun r b => ⌜r = true ∧ l.Any₂ (fun a b => a + b = 0)⌝)
    (onContinue := fun traversalState seen =>
      ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ ¬traversalState.prefix.Any₂ (fun a b => a + b = 0)⌝)
  with simp_all <;> grind
