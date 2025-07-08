/-- 素数であるという命題 -/
@[simp]
def IsPrime (n : Nat) := 1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

@[grind ->]
theorem IsPrime_pos (n : Nat) (h : IsPrime n) : 1 < n := by
  simp_all

/-- 1より大きい任意の数は素因数を持つ -/
theorem exists_prime_factor (n : Nat) (hgt : 1 < n) :
  ∃ k, IsPrime k ∧ k ∣ n := by
  -- nが素数であるかどうかによって場合分けをする。
  by_cases hprime : IsPrime n
  case pos =>
    -- nが素数であるときは明らか。
    grind [Nat.dvd_refl]

  -- 以下、nは素数でないとする。
  -- nは素数ではないのでnより真に小さい約数を持つ。
  have ⟨k, _, _, _⟩ : ∃ k, 1 < k ∧ k < n ∧ k ∣ n := by
    simp_all

  -- 帰納的に、k には素因数が存在するとしてよい。
  have := exists_prime_factor k (by assumption)

  -- k ∣ n なので、k に素因数があるなら n にも存在する。
  grind [Nat.dvd_trans]


/-- 階乗関数 -/
@[grind]
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

@[inherit_doc factorial] notation:max n "!" => factorial n

/-- 階乗は常に正 -/
@[grind <=]
theorem factorial_pos (n : Nat) : 0 < n ! := by
  induction n with grind

/-- 1 ≤ k ≤ n なら k は n! の約数 -/
@[grind ←]
theorem dvd_factorial (n : Nat) {k : Nat} (hk : k ≤ n) (kpos : 0 < k) : k ∣ (n !) := by
  induction n with grind [Nat.dvd_mul_right, Nat.dvd_mul_left_of_dvd, factorial]

/-- 素数は無限に存在する -/
theorem InfinitudeOfPrimes : ∀ n, ∃ p > n, IsPrime p := by
  -- n が与えられたとする。
  intro n
  -- このとき n! + 1 の素因数 p を考える。
  have : 1 < n ! + 1 := by grind
  obtain ⟨p, hp, _⟩ := exists_prime_factor (n ! + 1) this

  -- p は素数なので、p > n を示せばよい。
  suffices p > n from by grind

  -- 仮に p ≤ n だとする。
  suffices ¬ (p ≤ n) from by grind
  intro hle

  -- このとき p は n! の約数である。
  have hpdvd : p ∣ n ! := by grind

  -- p は n! + 1 の約数でもあるので、したがって p は 1 の約数であることになる。
  have : p ∣ 1 := by
    rw [show 1 = (n ! + 1) - n ! from by grind]
    grind [Nat.dvd_sub]

  -- つまり、p = 1 である。
  -- これは p が素数であることに矛盾する。
  grind [Nat.dvd_one]
