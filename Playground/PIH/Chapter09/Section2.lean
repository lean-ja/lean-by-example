/-- 許されている演算の集合 -/
inductive Op where
  /-- 加法 -/
  | add
  /-- 減法 -/
  | sub
  /-- 乗法 -/
  | mul
  /-- 除法 -/
  | div

instance : ToString Op :=
  ⟨Op.toString⟩
where
  Op.toString : Op → String
    | Op.add => "+"
    | Op.sub => "-"
    | Op.mul => "*"
    | Op.div => "/"

/-- 正の自然数。途中の状態として許可されるのは正の自然数のみ。 -/
abbrev Pos := { n : Nat // n > 0 }

private def Pos.ofNat (n : Nat) : Pos :=
  if h : n = 0 then ⟨1, by decide⟩
  else ⟨n, by omega⟩

instance {n : Nat} : OfNat Pos (n + 1) := ⟨Pos.ofNat (n + 1)⟩

instance : ToString Pos := inferInstance

/-- **Note** 9.9 における追記。
演算の可換性や単位元の法則を使って式を絞り込む valid -/
def Op.valid' (op : Op) (x y : Pos) : Bool :=
  match op with
  | Op.add => x.val ≤ y.val
  | Op.sub => x.val > y.val
  | Op.mul => x.val != 1 && y.val != 1 && x.val ≤ y.val
  | Op.div => y.val != 1 && x.val % y.val == 0

/-- `op` を適用したときに正の整数が生成されるかどうかチェックする

**Note** 本では引数の型は `Int` になっているが、文脈からして型は `Pos` であるべきだと考えられる。
-/
@[implemented_by Op.valid']
def Op.valid (op : Op) (x y : Pos) : Bool :=
  match op with
  | Op.add => true
  | Op.sub => x.val > y.val
  | Op.mul => true
  | Op.div => x.val % y.val == 0

/-- 有効な演算子の適用を実行する -/
def Op.apply (op : Op) (x y : Pos) : Nat :=
  match op with
  | Op.add => x.val + y.val
  | Op.sub => x.val - y.val
  | Op.mul => x.val * y.val
  | Op.div => x.val / y.val

open Lean in

/-- `x : Pos` をゴールおよび仮定から消してしまって、`x : Nat` と `x.pos : x > 0` にバラす。 -/
macro "unfold_pos" x:ident : tactic => do
  let x' := mkIdent x.getId
  let x'pos := mkIdent (x.getId ++ `pos)
  let tacSeq ← `(tactic| with_reducible
    all_goals
      have $x'pos : Subtype.val $x > 0 := Subtype.property $x
      generalize hx : Subtype.val $x = $x'
      simp only [hx] at *
      clear hx)
  return tacSeq

/-- `op.valid x y` が成立しているならば、`op.apply x y` は正の数 -/
theorem Op.pos_of_valid (op : Op) (x y : Pos) (h : op.valid x y) : op.apply x y > 0 := by
  dsimp [Op.apply, Op.valid] at *
  cases op <;> dsimp at *

  -- `x y : Pos` を正という情報だけ取り出して展開して、`x y : Nat` にする。
  -- これで `Pos` の項を消すことができる。
  unfold_pos x
  unfold_pos y

  case add => omega
  case mul => apply Nat.mul_pos <;> assumption
  case sub =>
    have : x > y := by simp_all
    omega
  case div =>
    suffices hyp : x / y ≠ 0 from by
      exact Nat.zero_lt_of_ne_zero hyp
    intro hyp
    have : y * (x / y) = x := by
      have : y ∣ x := by
        apply Nat.dvd_of_mod_eq_zero
        simp_all
      simp [Nat.mul_div_cancel' this]
    rw [hyp, Nat.mul_zero] at this
    omega

/-- `Op.apply` の返り値が `Pos` になっているバージョン -/
def Op.vapply (op : Op) (x y : Pos) (h : op.valid x y := by assumption) : Pos :=
  ⟨op.apply x y, Op.pos_of_valid op x y h⟩
