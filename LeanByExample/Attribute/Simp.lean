/- # simp

`[simp]` 属性を定理に付与すると、[`simp`](#{root}/Tactic/Simp.md) タクティクによって単純化ルールとして使用されるようになります。
-/

/-- 標準の`Nat`を真似て自作した型 -/
inductive MyNat where
  | zero
  | succ (n : MyNat)

/-- `MyNat`上の足し算 -/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n => succ (add m n)

instance : Add MyNat where
  add := MyNat.add

instance : Zero MyNat where
  zero := MyNat.zero

theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by
  rfl

-- 最初は`simp`で示すことができない
/-⋆-//-- error: simp made no progress -/
#guard_msgs in --#
example (n : MyNat) : (n + 0) + 0 = n := by
  simp

-- `[simp]`属性を付与する
attribute [simp] MyNat.add_zero

-- `simp`で示せるようになった！
example (n : MyNat) : (n + 0) + 0 = n := by
  simp

/- ## simp 補題の優先順位

`simp` 補題による単純化は、おおむね「内側から外側へ」という順序で行われます。
これはオプションで`simp`のトレース情報を出力させてみると確認できます。
-/

/-- フィボナッチ数列 -/
def Nat.fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => Nat.fib (n + 1) + Nat.fib n

@[simp]
theorem Nat.fib_zero : Nat.fib 0 = 0 := by
  rfl

set_option trace.Meta.Tactic.simp true in

-- 内側から外側へという順序で単純化を行っていることがわかる。
/-⋆-//--
trace: [Meta.Tactic.simp.rewrite] Nat.fib_zero:1000:
      Nat.fib 0
    ==>
      0
[Meta.Tactic.simp.rewrite] Nat.add_zero:1000:
      0 + 0
    ==>
      0
[Meta.Tactic.simp.rewrite] Nat.mul_zero:1000:
      37 * 0
    ==>
      0
[Meta.Tactic.simp.rewrite] eq_self:1000:
      0 = 0
    ==>
      True
-/
#guard_msgs in --#
theorem foo : 37 * (Nat.fib 0 + 0) = 0 := by
  simp
