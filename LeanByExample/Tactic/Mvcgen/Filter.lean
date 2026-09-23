import Lean

variable {α : Type}

/-- `continue` 文を使って実装した `Array.filter` -/
def Array.filterDo (p : α → Bool) (l : Array α) : Array α := Id.run do
  let mut res : Array α := #[]
  for x in l do
    if ! p x then
      continue
    res := res.push x
  return res

-- 証明のための補題を用意する
attribute [grind =] Array.toList_inj
attribute [grind _=_] Array.toList_filter

open Std.WP

-- `vcgen` が実験的機能であることを明示する
set_option experimental.vcgen true in

theorem Array.filterDo_spec (p : α → Bool) (l : Array α) :
    l.filterDo p = l.filter p := by
  generalize h : l.filterDo p = r
  apply Id.of_run_eq_wp h

  vcgen invariants
  · fun pref _ res => res.toList = pref.filter p
  with finish
