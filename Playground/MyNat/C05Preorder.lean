import Playground.MyNat.C04AddCancel

/- # MyNat が PreOrder であることを示す -/

/-- 自然数上の広義の順序関係 -/
protected inductive MyNat.le (n : MyNat) : MyNat → Prop
  /-- ∀ n, n ≤ n -/
  | refl : MyNat.le n n
  /-- `n ≤ m`ならば`n ≤ m + 1` -/
  | step {m : MyNat} : MyNat.le n m → MyNat.le n (m + 1)

/-- `MyNat.le`を`≤`で表せるようにする -/
instance : LE MyNat where
  le := MyNat.le

@[induction_eliminator]
def MyNat.le.recAux {n b : MyNat}
    {motive : (a : MyNat) → n ≤ a → Prop}
    (refl : motive n MyNat.le.refl)
    (step : ∀ {m : MyNat} (a : n ≤ m), motive m a → motive (m + 1) (MyNat.le.step a))
    (t : n ≤ b) :
  motive b t := by
  induction t with
  | refl => exact refl
  | @step c h ih =>
    exact step (a := h) ih

/-- 反射律 -/
@[refl, simp, grind <=]
theorem MyNat.le_refl (n : MyNat) : n ≤ n := by
  exact MyNat.le.refl

-- m, n, k はMyNatの項とする
variable {m n k : MyNat}

@[grind →]
theorem MyNat.le_step (h : n ≤ m) : n ≤ m + 1 := by
  apply MyNat.le.step
  exact h

/-- 推移律 -/
@[grind →]
theorem MyNat.le_trans (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  induction hmk with grind

/-- `MyNat.le`を「推移的な二項関係」として登録する -/
instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyNat.le_trans

open Lean Grind

instance : Preorder MyNat where
  le := (· ≤ ·)
  le_refl := MyNat.le_refl
  le_trans := MyNat.le_trans
