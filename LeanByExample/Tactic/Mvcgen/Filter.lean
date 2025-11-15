import Lean

variable {α : Type}

/-- `continue` 文を使って実装した `List.filter` -/
def List.filterDo (p : α → Bool) (l : List α) : List α := Id.run do
  let mut res : List α := []
  for x in l do
    if ! p x then
      continue
    res := res ++ [x]
  return res

open Std.Do

set_option mvcgen.warning false

theorem List.filterDo_spec (p : α → Bool) (l : List α) :
    l.filterDo p = l.filter p := by
  generalize h : l.filterDo p = r
  apply Id.of_wp_run_eq h

  mvcgen invariants
  · ⇓⟨cursor, res⟩ => ⌜res = cursor.prefix.filter p⌝
  with grind
