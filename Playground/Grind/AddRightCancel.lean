open Lean Grind

variable {M : Type} [Add M] [AddRightCancel M]

set_option warn.sorry false in --#

example : ∀ (a b c : M), a + c = b + c → a = b := by
  -- `grind`は本来このゴールを閉じることができるべきだと思うが、現状はできない。
  fail_if_success grind
  sorry
