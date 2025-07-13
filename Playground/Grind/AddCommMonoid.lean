
open Lean Grind

variable {M : Type} [AddCommMonoid M]

example (l m n : M) : l + m + n = (l + m) + n := by
  -- これは示すことができる
  grind

set_option warn.sorry false in

example (l m n : M) : l + m = m + l := by
  -- `grind`は本来このゴールを閉じることができるべきだと思うが、現状はできない。
  fail_if_success grind
  sorry
