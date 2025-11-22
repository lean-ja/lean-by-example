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
example (n : MyNat) : (n + 0) + 0 = n := by
  fail_if_success simp

  rw [MyNat.add_zero n]
  rw [MyNat.add_zero n]

-- `[simp]`属性を付与する
attribute [simp] MyNat.add_zero

-- `simp`で示せるようになった！
example (n : MyNat) : (n + 0) + 0 = n := by
  simp

/- ## 関数に付与した場合

`[simp]` 属性は定理だけでなく関数定義などにも付与することができます。関数定義に付与した場合、その関数について定義からただちに従う関数等式が自動的に見出だされて `simp` 補題として登録されます。

{{#include ./Simp/SimpAtDef.md}}
-/

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
example : 37 * (Nat.fib 0 + 0) = 0 := by
  simp

/- ## [simp←]

`simp` 補題は通常「左辺を右辺に」単純化するために使用されますが、逆方向に使用したい場合は `[simp←]` とします。

{{#include ./Simp/SimpLeft.md}}
-/

/- ## [simp↓]

`simp` はデフォルトでは部分式をすべて単純化した後に全体の式に単純化を適用しています。`simp` タクティクに、部分式が単純化されるよりも先に前処理として単純化したいルールがある場合は、`[simp↓]` を使用します。

{{#include ./Simp/SimpDown.md}}
-/

/- ## 優先度指定

`simp` 補題の中でも早い段階で適用してほしい補題や、遅い段階で適用してほしい補題があるとき、優先度を指定することができます。

### simp high

`[simp high]` とすると優先度が高まり、他の `simp` 補題よりも先に適用されるようになります。

{{#include ./Simp/SimpHigh.md}}
-/

/- ### simp low

`[simp low]` とすると優先度が低くなり、他の `simp` 補題よりも後に適用されるようになります。

{{#include ./Simp/SimpLow.md}}
-/
