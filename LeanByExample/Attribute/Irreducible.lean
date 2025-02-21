/- # irreducible -/

def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | m + 1 => (m + 1) * factorial m

-- 最初は rfl が通る
example : factorial 5 = 120 := by rfl

section
  -- [irreducible]属性を与える
  attribute [local irreducible] factorial

  /--
  error: tactic 'rfl' failed, the left-hand side
    factorial 5
  is not definitionally equal to the right-hand side
    120
  ⊢ factorial 5 = 120
  -/
  #guard_msgs (whitespace := lax) in
  example : factorial 5 = 120 := by
    rfl

end
