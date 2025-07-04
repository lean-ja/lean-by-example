import Playground.SeeCmd

/-- 群 -/
class Group (G : Type) [One G] [Mul G] [Inv G] where
  one_mul : ∀ g : G, g * 1 = g
  mul_one : ∀ g : G, 1 * g = g
  mul_inv : ∀ g : G, g * g⁻¹ = 1
  inv_mul : ∀ g : G, g⁻¹ * g = 1
  mul_assoc : ∀ g₁ g₂ g₃ : G, g₁ * (g₂ * g₃) = (g₁ * g₂) * g₃

variable {G : Type} [One G] [Mul G] [Inv G] [Group G]

attribute [grind] Group
attribute [simp] Group.one_mul Group.mul_one Group.mul_inv Group.inv_mul

@[grind]
theorem mul_right_inv {g h : G} (hy : g * h = 1) : h = g⁻¹ := calc
  _ = 1 * h := by grind
  -- _ = (g⁻¹ * g) * h := by grind
  -- _ = g⁻¹ * (g * h) := by grind
  -- _ = g⁻¹ * 1 := by grind
  _ = g⁻¹ := by grind

@[grind]
theorem mul_left_inv {g h : G} (hy : h * g = 1) : h = g⁻¹ := calc
  _ = h * 1 := by grind
  _ = g⁻¹ := by grind

@[simp, grind]
theorem inv_inv (g : G) : g⁻¹⁻¹ = g := by
  grind
