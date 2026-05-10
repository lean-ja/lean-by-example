
theorem Nat.zero_of_divide_lt_right {a b c : Nat} (hac : c < a) (h : a * b = c) :
    b = 0 ∧ c = 0 := by
  cases b with grind

-- invalid pattern というエラーになり、登録できない
-- これは等式をパターンとして登録しようとしたため
/-⋆-//--
error: invalid pattern, (non-forbidden) application expected
  @Eq (Nat) (@HMul.hMul (Nat) (Nat) (Nat) (@instHMul (Nat) (instMulNat)) #4 #3) #2
-/
#guard_msgs in --#
grind_pattern Nat.zero_of_divide_lt_right => c < a, a * b = c

-- 等式を避ければパターンとして登録できる
grind_pattern Nat.zero_of_divide_lt_right => c < a, a * b where
  guard a * b = c

/-- 割り算と剰余の定理の、一意性パート -/
theorem Int.division_with_remainder_unique {a b q r q' r' : Int} (hb : 0 < b)
    (h : a = b * q + r) (hr : 0 ≤ r) (hrb : r < b)
    (h' : a = b * q' + r') (hr' : 0 ≤ r') (hrb' : r' < b) :
    q = q' ∧ r = r' := by

  -- 両辺引いて、以下の等式を得る。
  have h_abs_eq : b.natAbs * (q - q').natAbs = (r' - r).natAbs := by
    grind only [natAbs_eq_iff_mul_eq_zero]

  -- `0 ≤ r < b` と `0 ≤ r' < b` から、`|r' - r| < b` が成り立つ
  have : (r' - r).natAbs < b.natAbs := by grind

  -- `0 < b` と `|r' - r| < b` から、`q - q' = 0` が成り立つ
  have : (q - q').natAbs = 0 := by
    -- ここで grind_pattern で登録した上記の定理を使用している
    grind only [usr Nat.zero_of_divide_lt_right]
  have q_eq_q' : q - q' = 0 := by grind

  -- さらに `r = a - b * q` と `r' = a - b * q'` より `r = r'` が成り立つ。
  have r_eq_r' : r = r' := by
    grind

  grind only
