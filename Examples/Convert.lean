import Mathlib.Tactic.Convert

variable (a b c: Nat)

/-! ## convert -/

example (f : Nat → Nat) (h : f (a + b) = 0) (hc: a + b = c) : f (c) = 0 := by
  -- `h` はゴールと等しくないので失敗する
  try exact [h]

  -- `h` とゴールの差分を新たなゴールにする
  convert h

  -- ゴールが `⊢ c = a + b` に変わっている
  show c = a + b

  rw [hc]
