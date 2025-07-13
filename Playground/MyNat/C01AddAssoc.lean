import Playground.SeeCmd

/-- 自前で実装した自然数 -/
inductive MyNat where
  /-- ゼロ -/
  | zero
  /-- 後者関数（`n`に対して`n + 1`を返す関数） -/
  | succ (n : MyNat)

/-- `MyNat`同士の足し算 -/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n => succ (add m n)

instance : Add MyNat where
  add := MyNat.add

/-- `Nat`の項から対応する`MyNat`の項を得る
ただし`Nat`はLean組み込みの自然数の型 -/
def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => MyNat.zero
  | n + 1 => MyNat.succ (MyNat.ofNat n)

/-- `OfNat`のインスタンスを実装する -/
@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

/-- `MyNat`用の帰納法の原理を書き直したもの -/
@[induction_eliminator]
def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n : MyNat) → motive n → motive (n + 1)) (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

@[grind =, simp]
theorem MyNat.ctor_succ (n : MyNat) : MyNat.succ n = n + 1 := by
  rfl

/-- `MyNat`型の項をLean組み込みの`Nat`の項に変換する
注意：返り値の型はLean標準の`Nat` -/
def MyNat.toNat (n : MyNat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => MyNat.toNat n + 1

instance : Repr MyNat where
  reprPrec n _ := repr n.toNat

/-- 0 を右から足しても変わらない -/
@[grind =, simp]
theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by rfl

/-- 右のオペランドに付いた`.succ`は外側に出せる -/
@[grind =, simp]
theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by
  rfl

/-- `add_succ`の`· + 1`版 -/
@[grind =]
theorem MyNat.add_one (m n : MyNat) : m + (n + 1) = (m + n) + 1 := by
  rfl

/-- 左のオペランドに付いた`.succ`は外側に出せる -/
@[grind =, simp]
theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with grind

/-- `succ_add`の`· + 1`版 -/
@[grind =]
theorem MyNat.one_add (m n : MyNat) : (m + 1) + n = (m + n) + 1 := by
  induction n with grind

/-- 0を左から足しても変わらない -/
@[grind =, simp]
theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n with grind

/-- 足し算の交換法則 -/
@[grind _=_]
theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with grind

/-- 足し算の結合法則 -/
@[grind _=_]
theorem MyNat.add_assoc (l m n : MyNat) : l + m + n = l + (m + n) := by
  induction n with grind

-- `MyNat`の足し算が結合法則を満たすことを登録する
instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc

-- `MyNat`の足し算が交換法則を満たすことを登録する
instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm

-- **TODO** なぜかインスタンスを追加しても効果がない。原因を調べたい。
-- ただのバグならよいが、仕様だったら調べるべき。
-- instance : Lean.Grind.AddCommMonoid MyNat where
--   add_zero := MyNat.add_zero
--   add_assoc := MyNat.add_assoc
--   add_comm := MyNat.add_comm

example (l m n : MyNat) : l + m + n + 3 = m + (l + n) + 3 := by
  grind
