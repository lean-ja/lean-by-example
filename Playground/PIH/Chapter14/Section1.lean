/- # モノイド -/

/-- モノイド -/
class Monoid (α : Type) where
  /-- 単位元 -/
  unit : α

  /-- 演算 -/
  op : α → α → α

  /-- 結合法則 -/
  assoc : ∀ x y z : α, op (op x y) z = op x (op y z)

section
  /- ## 優先度を指定しないインスタンスを２つ重ねた例 -/

  local instance : Monoid Nat where
    unit := 0
    op x y := x + y
    assoc x y z := by ac_rfl

  local instance : Monoid Nat where
    unit := 1
    op x y := x * y
    assoc x y z := by ac_rfl

  -- 後から宣言した方が優先される
  #guard (Monoid.unit : Nat) = 1
end

section
  local instance : Monoid Nat where
    unit := 0
    op x y := x + y
    assoc x y z := by ac_rfl

  local instance (priority := low) : Monoid Nat where
    unit := 1
    op x y := x * y
    assoc x y z := by ac_rfl

  -- 後から宣言した方が優先されなくなる！
  #guard (Monoid.unit : Nat) = 0
end

section
  local instance (priority := high) : Monoid Nat where
    unit := 0
    op x y := x + y
    assoc x y z := by ac_rfl

  local instance : Monoid Nat where
    unit := 1
    op x y := x * y
    assoc x y z := by ac_rfl

  -- 後から宣言した方が優先されなくなる！
  #guard (Monoid.unit : Nat) = 0
end
