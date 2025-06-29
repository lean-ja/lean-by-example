import Mathlib.Tactic --#
/- # simp

`simp` は、ターゲットを決められた規則に基づいて自動で単純化（simplify）するタクティクです。

基本的には、`A = B` または `P ↔ Q` という形の補題を登録しておくと、`A` を `B` に、または `P` を `Q` に自動で単純化してくれます。等価性に基づいて書き換えるので [`rw`](#{root}/Tactic/Rw.md) タクティクと似ていますが、`rw` と異なり必ずしも明示的に書き換えルールを引数として与える必要がありません。

[`[simp]`](#{root}/Attribute/Simp.md) 属性を付けることにより単純化に使ってほしい命題を登録することができます。-/

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

@[simp]
theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by
  rfl

@[simp]
theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 0 + n.succ = (0 + n).succ from by rfl]
    rw [ih]

example (n : MyNat) : (0 + n + 0) + 0 = n := by
  -- 単に`simp`と書くだけで自動的に登録した補題が使用される
  simp

/- ## 等式・同値性以外のルールを登録した場合

等式や同値性以外のルールを登録した場合、等式・同値性への変換が自動的に行われたうえで登録されます。

たとえば下記の例のように、`1 ≠ 0` というルールを `simp` 補題として登録した場合、`(1 = 0) = False` という定理が自動生成されそれに基づいて単純化が行われるようになります。
-/

instance : One MyNat where
  one := MyNat.succ MyNat.zero

theorem MyNat.one_neq_zero : (1 : MyNat) ≠ 0 := by
  intro h
  injection h

-- `simp`属性を追加したことによって、
/-⋆-//--
info: theorem MyNat.one_neq_zero._proof_1 : (1 = 0) = False :=
eq_false MyNat.one_neq_zero

-- Lean.Meta.simpExtension extension: 1 new entries
-/
#guard_msgs in --#
whatsnew in attribute [simp] MyNat.one_neq_zero

example (h : (1 : MyNat) = 0) (P : Prop) : P := by
  simp at h

/- 一般に `P` という命題を登録すると `P = True` という定理が、`¬ P` という命題を登録すると `P = False` という定理が自動生成されて単純化に使用されます。-/

/-- 偶数を表す帰納的述語 -/
inductive MyEven : Nat → Prop where
  | zero : MyEven 0
  | step (n : Nat) : MyEven n → MyEven (n + 2)

theorem MyEven_two : MyEven 2 := by
  apply MyEven.step
  apply MyEven.zero

-- `MyEven 2 = True` という書き換えルールが自動生成されている
/-⋆-//--
info: theorem MyEven_two._proof_1 : MyEven 2 = True :=
eq_true MyEven_two

-- Lean.Meta.simpExtension extension: 1 new entries
-/
#guard_msgs in --#
whatsnew in attribute [simp] MyEven_two

/- ## simp で使用できる構文

### 補題の指定
既知の `h : P` という命題を使って単純化させたいときは、明示的に `simp [h]` と指定することで可能です。複数個指定することもできます。また `simp only [h₁, ... , hₖ]` とすると `h₁, ... , hₖ` だけを使用して単純化を行います。-/

example {P Q : Prop} (h : Q) : (P → P) ∧ Q := by
  simp only [imp_self, true_and]
  assumption

/- 単に名前を定義に展開したい場合は [`dsimp`](./Dsimp.md) を使用します。

### at 構文

`simp` は [at 構文](#{root}/Parser/AtLocation.md) を受け入れます。`simp` は何も指定しなければゴールを単純化しますが、ローカルコンテキストにある `h : P` を単純化させたければ `simp at h` と指定することで可能です。ゴールと `h` の両方を単純化したいときは `simp at h ⊢` とします。-/

example {n m : Nat} (h : n + 0 + 0 = m) : n = m + (0 * n) := by
  simp only [add_zero, zero_mul] at h ⊢
  assumption

/- ローカルコンテキストとゴールをまとめて全部単純化したい場合は `simp at *` とします。 -/

/- ## 注意点: simp 補題のループ

なお、`[simp]` 属性を付与した命題は「左辺を右辺に」単純化するルールとして登録されます。
左辺と右辺を間違えて登録すると、無限ループになって `simp` の動作が破壊されることがあります。`[simp]` 属性は慎重に登録してください。-/
section

  -- 何もしていなければ simp で通る
  example (n m : Nat) : (n + 0) * m = n * m := by simp

  -- 良くない simp 補題の例
  -- 「左辺を右辺に」単純化するため、かえって複雑になってしまう
  -- なお local を付けているのは、この simp 補題登録の影響をセクション内に限定するため
  @[local simp]
  theorem bad_add_zero (n : Nat) : n = n + 0 := by rw [Nat.add_zero]

  -- 今まで通った証明が通らなくなる
  /-⋆-//--
  error: tactic 'simp' failed, nested error:
  maximum recursion depth has been reached
  use `set_option maxRecDepth <num>` to increase limit
  use `set_option diagnostics true` to get diagnostic information
  -/
  #guard_msgs (whitespace := lax) in --#
  example (n m : Nat) : (n + 0) * m = n * m := by simp

end

/- ## arith オプション
`simp` の設定で `arith` を有効にすると、算術的な単純化もできるようになります。
-/
set_option linter.flexible false in --#

example (x y : Nat) : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  -- `simp` だけでは証明が終わらない
  fail_if_success solve
  | simp

  -- 適当に証明する
  suffices y ≤ x + y + 1 from by
    simp_all

  have : y ≤ x + y + 1 := calc
    _ = 0 + y := by simp
    _ ≤ x + 1 + y := by gcongr; simp
    _ = x + y + 1 := by ac_rfl
  assumption

example {x y : Nat} : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  -- config を与えれば一発で終わる
  simp +arith

/- ## 関連タクティク -/
/- ### simpa
`simpa` は、`simp` を実行した後 `assumption` を実行するという一連の流れを一つのタクティクにしたものです。`simpa at h` 構文は存在せず、`simpa using h` と書くことに注意してください。-/

example (P : Prop) (h : P) : True → P := by
  simpa

example {n m : Nat} (h : n + 0 + 0 = m) : n = m := by
  simpa using h

/- ### simp?

`simp` は自動的に証明を行ってくれますが、何が使われたのか知りたいときもあります。`simp?` は単純化に何が使われたのかを示してくれるので、`simp only` などを用いて明示的に書き直すことができます。-/

/-⋆-//-- info: Try this: simp only [forall_const, imp_self, or_true] -/
#guard_msgs in --#
example (P : Prop) : (True → P) ∨ (P → P) := by
  simp?

/- ### simp_all
[`simp_all`](./SimpAll.md) はローカルコンテキストとゴールをこれ以上単純化できなくなるまですべて単純化します。-/

example {P Q : Prop} (hP : P) (hQ : Q) : P ∧ (Q ∧ (P → Q)) := by
  -- simp at * は失敗する
  fail_if_success simp at *

  simp_all
