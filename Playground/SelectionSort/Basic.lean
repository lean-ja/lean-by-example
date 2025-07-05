import Mathlib.Tactic

universe u

open List

variable {α : Type u} [LinearOrder α]


def List.selection_sort (l : List α) : List α :=
  if hl : 0 < l.length then
    let μ : α := minimum_of_length_pos hl

    have mem : μ ∈ l := by
      apply minimum_mem
      simp_all only [coe_minimum_of_length_pos, μ]

    let rest := l.erase μ

    have _decrease : l.length > rest.length := calc
      l.length
      _ = rest.length + 1 := by rw [← length_erase_add_one mem]
      _ > rest.length := by linarith

    μ :: (selection_sort rest)
  else
    []

theorem perm_selection_sort (l : List α) : l ~ selection_sort l := by
  induction' ih : l.length generalizing l

  all_goals
    unfold selection_sort
    simp_all

  case succ n IH =>
    set μ := minimum_of_length_pos (_ : 0 < length l)
    set rest := l.erase μ

    have mem : μ ∈ l := by
      apply minimum_mem
      simp_all only [coe_minimum_of_length_pos, μ]

    have rlen : rest.length = n := by
      convert List.length_erase_of_mem mem
      simp only [ih]
      omega

    have hr : selection_sort rest ~ rest := by
      exact Perm.symm (IH rest rlen)

    suffices l ~ μ :: rest from by
      apply this.trans
      simp only [perm_cons, hr.symm]

    exact perm_cons_erase mem

theorem sorted_selection_sort (l : List α) : Sorted (· ≤ ·) l.selection_sort := by
  induction' ih : l.length generalizing l

  all_goals
    unfold selection_sort
    simp_all

  case succ n IH =>
    set μ := minimum_of_length_pos (_ : 0 < length l)
    set rest := l.erase μ

    have rsub : rest ⊆ l := by
      exact erase_subset

    have rperm : selection_sort rest ~ rest := by
      exact Perm.symm (perm_selection_sort rest)

    have subh : selection_sort rest ⊆ l := by
      exact (Perm.subset_congr_left (id (Perm.symm rperm))).mp rsub

    constructor
    · show ∀ (b : α), b ∈ selection_sort rest → minimum l ≤ ↑b
      intro b hb
      exact minimum_le_of_mem' (subh hb)
    · apply IH rest

      have mem : μ ∈ l := by
        apply minimum_mem
        simp_all only [coe_minimum_of_length_pos, rest, μ]

      convert List.length_erase_of_mem mem
      simp only [ih]
      omega
