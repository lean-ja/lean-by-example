/- # ring_nf

`ring_nf` は、[`ring`](./Ring.md) タクティクの変種で、等式を証明する代わりに式を標準形に変形します。

`ring_nf` は部分項の変形を行うことができます。
-/
import Mathlib.Tactic.Ring

example {x y : Rat} (F : Rat → Rat) : F (x + y) + F (y + x) = 2 * F (x + y) := by
  ring_nf

example {x y : Int} (h : x + y - x = -2) : y = -2 := by
  ring_nf at h

  assumption
