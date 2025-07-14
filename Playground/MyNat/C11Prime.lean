import Playground.MyNat.C10Dvd

namespace MyNat

/-- 素数。１より大きく、自分自身と１以外で割り切れない数 -/
@[simp, grind]
def IsPrime (n : MyNat) : Prop :=
  n > 1 ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

-- **TODO**: 適切な場所に移動させる
theorem not_lt_zero (n : MyNat) : ¬n < 0 := by grind

-- **TODO**: 適切な場所に移動させる
theorem le_of_succ_le_succ {n m : MyNat} : n.succ ≤ m.succ → n ≤ m := by
  induction n with grind

-- **TODO**: 証明を考え直す
instance lt_wfRel : WellFoundedRelation MyNat where
  rel := (· < ·)
  wf := by
    apply WellFounded.intro
    intro n
    induction n with
    | zero =>
      apply Acc.intro 0
      intro y h
      apply absurd h (MyNat.not_lt_zero _)
    | succ n ih =>
      apply Acc.intro (MyNat.succ n)
      intro m h
      have : m = n ∨ m < n := MyNat.eq_or_lt_of_le (MyNat.le_of_succ_le_succ (by grind))
      match this with
      | Or.inl e => subst e; assumption
      | Or.inr e => exact Acc.inv ih e

noncomputable def strongRecOn.{u}
    {motive : MyNat → Sort u}
    (n : MyNat)
    (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive n :=
  MyNat.lt_wfRel.wf.fix ind n

-- **TODO** MyNat 上の well-founded recursion が使えないと fail to show termination になる
/-- 1より大きい任意の数は素因数を持つ -/
theorem exists_prime_factor (n : MyNat) (hgt : 1 < n) :
  ∃ k, IsPrime k ∧ k ∣ n := by
  induction n using strongRecOn with
  | ind n ih =>
    -- nが素数であるかどうかによって場合分けをする。
    by_cases hprime : IsPrime n
    case pos =>
      -- nが素数であるときは明らか。
      grind

    -- 以下、nは素数でないとする。
    -- nは素数ではないのでnより真に小さい約数を持つ。
    have ⟨k, _, _, _⟩ : ∃ k, 1 < k ∧ k < n ∧ k ∣ n := by
      simp_all

    -- 帰納的に、k には素因数が存在するとしてよい。
    have := ih k ‹k < n› ‹1 < k›

    -- k ∣ n なので、k に素因数があるなら n にも存在する。
    grind

/-- 階乗関数 -/
@[grind, simp]
def factorial : MyNat → MyNat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

@[inherit_doc factorial] notation:max n "!" => factorial n

@[grind =]
theorem factorial_succ (n : MyNat) : (n + 1)! = (n + 1) * n ! := by
  rfl

/-- 階乗は常に正 -/
@[grind <=]
theorem factorial_pos (n : MyNat) : 0 < n ! := by
  induction n with grind

#see Nat.add_le_add_iff_right
-- **TODO**: 適切な場所に移動させる
@[simp↓, grind =]
theorem MyNat.add_one_le_add_iff_right {m n : MyNat} : m + 1 ≤ n + 1 ↔ m ≤ n := by
  constructor <;> grind [MyNat.le_iff_add]

set_option warn.sorry false in --#

/-- 1 ≤ k ≤ n なら k は n! の約数 -/
@[grind →]
theorem dvd_factorial (n : MyNat) {k : MyNat} (hk : k ≤ n) (kpos : 0 < k) : k ∣ (n !) := by
  induction n with
  | zero =>
    grind
  | succ n ih =>
    have : k = n + 1 ∨ k ≤ n := by
      have : k = n + 1 ∨ k < n + 1 := by grind
      cases this with grind

    rcases this with eq | le
    · grind
    · replace ih := ih le
      rw [show (n + 1)! = (n + 1) * n ! from by rfl]
      grind

-- **TODO**: 適切な場所に移動させる
#see Nat.not_le
@[grind _=_]
theorem not_le (m n : MyNat) : ¬ n ≤ m ↔ m < n := by
  constructor <;> grind

/-- 素数は無限に存在する -/
theorem InfinitudeOfPrimes : ∀ n : MyNat, ∃ p > n, IsPrime p := by
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
  have hpdvd : p ∣ n ! := by
    apply dvd_factorial <;> grind

  -- p は n! + 1 の約数でもあるので、したがって p は 1 の約数であることになる。
  have : p ∣ 1 := by
    rw [show 1 = (n ! + 1) - n ! from by grind]
    grind [Nat.dvd_sub]

  -- つまり、p = 1 である。
  -- これは p が素数であることに矛盾する。
  grind

end MyNat
