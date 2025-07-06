def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

@[grind]
def factorialTR (n : Nat) : Nat :=
  aux n 1
where
  @[grind] aux (n acc : Nat) :=
    match n with
    | 0 => acc
    | n + 1 => aux n (acc * (n + 1))

@[grind =]
theorem factorialTR_lem (n acc : Nat) : factorialTR.aux n acc = acc * factorialTR.aux n 1 := by
  induction n generalizing acc with grind

@[grind =]
theorem factorial_tr_succ (n : Nat) : factorialTR (n + 1) = factorialTR n * (n + 1) := by
  grind

theorem factorial_eq_tr (n : Nat) : factorial n = factorialTR n := by
  fun_induction factorial <;> grind
