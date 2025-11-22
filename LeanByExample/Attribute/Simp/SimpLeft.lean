
/-- モノイド -/
class Monoid (α : Type) extends Mul α, One α where
  mul_one : ∀ a : α, a * 1 = a
  one_mul : ∀ a : α, 1 * a = a
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)

variable {α : Type} [Monoid α]

@[simp←]
theorem mul_one_rev (a : α) : a = 1 * a := by
  rw [Monoid.one_mul a]

-- `simp?` で確認してみると、該当する補題に `←` が付与されている
/-⋆-//--
info: Try this:
  [apply] simp only [← mul_one_rev]
-/
#guard_msgs in --#
example (a : α) : 1 * (1 * a) = a := by
  simp?
