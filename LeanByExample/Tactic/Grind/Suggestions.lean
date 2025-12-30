import Lean.LibrarySuggestions.Default

example {α : Type} (n : Nat) (xs : List α)
  (npos : 0 < n) (h : n < xs.length) :
    [] ≠ xs.take n := by
  fail_if_success grind -- ただの grind では示せないが…
  grind +suggestions
