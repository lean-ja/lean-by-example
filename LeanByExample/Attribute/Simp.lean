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
/-⋆-//-- error: `simp` made no progress -/
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

-- `simp`の行った書き換えを追跡する
set_option trace.Meta.Tactic.simp.rewrite true in

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

/- ## [simp] 属性で利用できる構文

### [simp←]

`simp` 補題は「左辺を右辺に」単純化するために使用されますが、逆方向に使用したい場合は `[simp←]` とします。
-/

@[simp←]
theorem MyNat.zero_add (n : MyNat) : n = 0 + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 0 + n.succ = (0 + n).succ from by rfl]
    rw [←ih]

-- 該当するsimp補題に `←` が付いている
/-⋆-//--
info: Try this:
  [apply] simp only [← MyNat.zero_add, MyNat.add_zero]
-/
#guard_msgs in --#
example (n : MyNat) : 0 + n + 0 = n := by
  simp?

/- ### [simp↓]

`simp` はデフォルトでは部分式をすべて単純化した後に全体の式に単純化を適用しています。
-/
section

-- `foo`定理をsimp補題として登録する
attribute [local simp] foo

-- `foo`を示そうとしているのに、単純化に`foo`が使用されていない！
-- これは、部分式が先に単純化されるため。
/-⋆-//--
info: Try this:
  [apply] simp only [Nat.fib_zero, Nat.add_zero, Nat.mul_zero]
-/
#guard_msgs (whitespace := lax) in --#
example : 37 * (Nat.fib 0 + 0) = 0 := by
  simp?

end
/- `simp` タクティクに、部分式が単純化されるよりも先に前処理として単純化したいルールがある場合は、`[simp↓]` を使用します。-/

attribute [simp↓] foo

-- `foo`が使われて終了するようになった！
/-⋆-//--
info: Try this:
  [apply] simp only [↓foo]
-/
#guard_msgs in --#
example : 37 * (Nat.fib 0 + 0) = 0 := by
  simp?

/- ### 優先度指定

`simp` 補題の中でも早い段階で適用してほしい補題や、遅い段階で適用してほしい補題があるとき、優先度を指定することができます。

#### simp high

`[simp high]` とすると優先度が高まり、他のsimp補題よりも先に適用されるようになります。
-/
section

theorem MyNat.zero_zero : (0 : MyNat) + 0 = 0 := by
  rfl

-- 普通にsimp補題に登録する
attribute [simp] MyNat.zero_zero

-- `simp`の行った書き換えを追跡する
set_option trace.Meta.Tactic.simp.rewrite true

-- `MyNat.zero_zero` が使用されていない。
-- これは部分式の単純化が優先されるため。
/-⋆-//--
trace: [Meta.Tactic.simp.rewrite] MyNat.add_zero:1000:
      0 + 0
    ==>
      0
[Meta.Tactic.simp.rewrite] eq_self:1000:
      0 = 0
    ==>
      True
-/
#guard_msgs (whitespace := lax) in --#
example : (0 : MyNat) + 0 = 0 := by
  simp

attribute [-simp] MyNat.add_zero -- 先ほどのsimp属性を削除する
attribute [simp high] MyNat.zero_zero -- `simp high` を指定し直す

-- デフォルトでは優先度は1000になるが、
-- highに指定すると優先度が10000になり、先に適用される
/-⋆-//--
trace: [Meta.Tactic.simp.rewrite] MyNat.zero_zero:10000:
      0 + 0
    ==>
      0
[Meta.Tactic.simp.rewrite] eq_self:1000:
      0 = 0
    ==>
      True
-/
#guard_msgs (whitespace := lax) in --#
example : (0 : MyNat) + 0 = 0 := by
  simp

end
