import Playground.SeeCmd

/-- 群 -/
class Group (G : Type) [One G] [Mul G] [Inv G] where
  /-- 単位元を右から掛けても変わらない -/
  mul_one : ∀ g : G, g * 1 = g
  /-- 単位元を左から掛けても変わらない -/
  one_mul : ∀ g : G, 1 * g = g
  /-- 元とその逆元を掛けると単位元になる -/
  mul_inv : ∀ g : G, g * g⁻¹ = 1
  /-- 逆元と元を掛けると単位元になる -/
  inv_mul : ∀ g : G, g⁻¹ * g = 1
  /-- 掛け算は結合的である -/
  mul_assoc : ∀ g₁ g₂ g₃ : G, g₁ * (g₂ * g₃) = (g₁ * g₂) * g₃

variable {G : Type} [One G] [Mul G] [Inv G] [Group G]

attribute [grind =>]
  Group.mul_one Group.one_mul
  Group.mul_inv Group.inv_mul Group.mul_assoc

set_option trace.grind.assert true
set_option trace.grind.debug.congr true
set_option trace.grind.ematch.instance true

@[grind =>]
theorem mul_right_inv {g h : G} (hy : g * h = 1) : h = g⁻¹ := calc
  _ = 1 * h := by grind
  -- _ = (g⁻¹ * g) * h := by grind
  -- _ = g⁻¹ * (g * h) := by grind
  -- _ = g⁻¹ * 1 := by grind
  _ = g⁻¹ := by grind

@[grind =>]
theorem mul_left_inv {g h : G} (hy : h * g = 1) : h = g⁻¹ := calc
  _ = h * 1 := by grind
  _ = g⁻¹ := by grind

@[grind =]
theorem inv_inv (g : G) : g⁻¹⁻¹ = g := by
  grind
