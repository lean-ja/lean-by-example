
/-- 謎の自然数 -/
opaque foo : Nat

/-- 謎の自然数 -/
opaque bar : Nat

/-- 謎の自然数 -/
opaque baz : Nat

@[simp]
axiom foo_eq_bar : foo = bar

@[simp]
axiom foo_eq_baz : foo = baz

set_option warn.sorry false in --#

example : foo = baz := by
  -- 先に宣言された方の `foo_eq_bar` が適用されてしまって、
  -- 証明することができない
  simp

  guard_target =ₛ bar = baz

  sorry

attribute [simp high] foo_eq_baz

example : foo = baz := by
  -- `foo_eq_baz` の方が優先度が高いため、こちらが先に適用される
  simp
