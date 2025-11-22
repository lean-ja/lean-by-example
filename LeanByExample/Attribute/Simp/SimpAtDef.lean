import Mathlib.Util.WhatsNew

/-- フィボナッチ数列 -/
def Nat.fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => Nat.fib (n + 1) + Nat.fib n

-- `rfl` ですぐ示せる関数等式があるが、`simp` では示せない
example : Nat.fib 0 = 0 := by
  fail_if_success simp
  rfl

example : Nat.fib 1 = 1 := by
  fail_if_success simp
  rfl

example (n : Nat) : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by
  fail_if_success simp
  rfl

-- `Nat.fib` に対する `simp` 補題を生成する
attribute [simp] Nat.fib

-- `simp` で示せるようになる!
example : Nat.fib 0 = 0 := by
  simp

example : Nat.fib 1 = 1 := by
  simp

example (n : Nat) : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by
  simp
