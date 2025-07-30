/- # なぜか[grind]属性が一切付与できない

[grind]属性が全く付与できない例を見つけたが、なぜなのか理解できない。
理由を教えてほしい。
-/

variable {A B C : Type}

theorem comp_eq {f : A → B} {g : B → C} {h : A → C} (heq : g ∘ f = h) (a : A) : g (f a) = h a := calc
  _ = (g ∘ f) a := rfl
  _ = h a := by rw [heq]

-- なぜか `[grind]` 属性が一切付与できない
/--
error: `@[grind] theorem comp_eq` failed to find patterns, consider using different options or the `grind_pattern` command
-/
#guard_msgs in
attribute [grind] comp_eq

/--
error: `@[grind =>] theorem comp_eq` failed to find patterns searching from left to right, consider using different options or the `grind_pattern` command
-/
#guard_msgs in
attribute [grind =>] comp_eq

/--
error: invalid pattern, (non-forbidden) application expected
  @#3 (@#4 #0)
-/
#guard_msgs in
attribute [grind =] comp_eq
