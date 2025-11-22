/- # simp

`simp` は、ターゲットを等式や同値性に基づいて自動で単純化（simplify）するタクティクです。

基本的には、`A = B` という形の補題を登録しておくと、`A` を `B` に自動で単純化します。左辺を右辺に書き換え、右辺を左辺に戻すことはないため、右辺は左辺よりも「単純」であることが求められます。等価性に基づいて書き換えるので [`rw`](#{root}/Tactic/Rw.md) タクティクと似ていますが、`rw` と異なり明示的に書き換えルールを引数として与えなくても自動で補ってくれます。

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
  -- 単に`simp`と書くだけで自動的に登録した補題によって書き換えが行われる
  simp

/- ## 同値性を扱う

等式 `A = B` の形をした補題だけでなく、同値性 `A ↔ B` の形をした補題も `simp` 補題として登録し、単純化に使用することができます。等式と同様に、`A` を `B` に単純化するのに使用されます。
-/

/-- 何かの命題 -/
opaque Foo : Prop

@[simp]
axiom foo_iff_true : Foo ↔ True

example : Foo := by
  -- `Foo` を `True` に単純化できる
  simp

/- ## simp の基本的な構文

### `[h₁, h₂, …]` で引数を渡す

既知の `h : P` という命題を使って単純化させたいときは、明示的に `simp [h]` と指定することで可能です。複数個指定することもできて、その場合はカンマ区切りで `simp [h₁, h₂, …]` とします。-/

/-- 0 っぽい何か -/
opaque zero : Nat

/-- １っぽい何か -/
opaque one : Nat

/-- `zero` に右から１を足すと `one` に等しい -/
axiom add_zero_one_eq_one : zero + 1 = one

example : zero + 1 = one := by
  -- 単に`simp`としても何も起こらない
  -- これは`simp`補題として登録していないから
  fail_if_success simp

  -- 明示的に引数として書き換えルールを与えれば証明が通る
  simp [add_zero_one_eq_one]

/-- `zero` 同士を足すと `zero` に等しい -/
axiom add_zero_zero_eq_zero : zero + zero = zero

example : (zero + zero) + 1 = one := by
  -- 複数の補題を指定することもできる
  simp [add_zero_zero_eq_zero, add_zero_one_eq_one]

/- ### simp only

`simp only [h₁, h₂, …]` と書くと、登録された補題は無視して、引数として与えた補題だけを使って単純化を行います。

{{#include ./Simp/SimpOnly.md}}
-/

/- ### at 構文

`simp` は [at 構文](#{root}/Syntax/AtLocation.md) を受け入れます。`simp` は何も指定しなければゴールを単純化しますが、ローカルコンテキストにある `h : P` を単純化させたければ `simp at h` と指定することで可能です。ゴールと `h` の両方を単純化したいときは `simp at h ⊢` とします。-/

example {n m : Nat} (h : n + 0 + 0 = m) : n = m + (0 * n) := by
  simp only [Nat.add_zero, Nat.zero_mul] at h ⊢
  assumption

/- ローカルコンテキストとゴールをまとめて全部単純化したい場合は `simp at *` とします。 -/

/- ## 等式・同値性以外の補題を扱う

等式や同値性以外の補題を登録した場合、等式・同値性への変換が自動的に行われたうえで登録されます。

たとえば下記の例のように、`1 ≠ 0` という命題を `simp` 補題として登録した場合、`(1 = 0) = False` という定理が自動生成されそれに基づいて単純化が行われるようになります。

{{#include ./Simp/OneNeqZero.md}}
-/

/- 一般に等式の形をしているとは限らない命題 `P : Prop` に対して `P` という命題を `simp` 補題として登録すると `P = True` という定理が、`¬ P` という命題を登録すると `P = False` という定理がそれぞれ自動生成されて単純化に使用されます。

{{#include ./Simp/MyEven.md}}
-/

/- ## simp 補題のループ

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
  error: Tactic `simp` failed with a nested error:
  maximum recursion depth has been reached
  use `set_option maxRecDepth <num>` to increase limit
  use `set_option diagnostics true` to get diagnostic information
  -/
  #guard_msgs (whitespace := lax) in --#
  example (n m : Nat) : (n + 0) * m = n * m := by simp

end
/-
なお `linter.loopingSimpArgs` オプションを有効にすると、`simp` 引数のループを検出して警告を出すようになります。
-/

-- ループを引き起こす `simp` の引数に対して警告を出す
set_option linter.loopingSimpArgs true in

/-⋆-//--
warning: Possibly looping simp theorem: `bad_add_zero`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
-/
#guard_msgs (warning, drop error) in --#
example (n m : Nat) : (n + 0) * m = n * m := by
  simp [bad_add_zero]

/- ## discharger について

`simp` 補題を適用するときに、補題が要求する前提条件を埋める仕組みのことを discharger と呼びます。`simp` のデフォルトの discharger はあまり強力ではありません。

以下の例では、`0 ≤ 1` という前提条件を自動では示すことができずに `simp` が失敗します。[^disch]
-/

theorem Nat.max_eq_left' {a b : Nat} (h : b ≤ a) : max a b = a := by
  grind

-- dischargeの過程を表示する
set_option trace.Meta.Tactic.simp.discharge true in

/-⋆-//--
trace: [Meta.Tactic.simp.discharge] Nat.max_eq_left' discharge ❌️
      0 ≤ 1
-/
#guard_msgs in --#
example : max 1 0 = 1 := by
  fail_if_success
    simp only [Nat.max_eq_left']

  grind

/- これは `decide` タクティクで示すことができるため、`(disch := ...)` という構文で `decide` タクティクを discharger に指定すれば証明が通るようになります。 -/

example : 0 ≤ 1 := by
  -- decide で証明できる
  decide

example : max 1 0 = 1 := by
  simp (disch := decide) only [Nat.max_eq_left']

/- ## 条件付き書き換えはできない

`simp` は「`A = B` という補題に基づいて `A` を `B` に書き換える」ということはできるのですが、「`C → A = B` という補題に基づいて `C` が成り立つときに `A` を `B` に書き換える」ということはできません。

discharger として `assumption` タクティクを指定すれば多少は証明が通るようになります。

{{#include ./Simp/CondRw.md}}
-/

/- ## arith オプション

`simp` の設定で `arith` を有効にすると、算術的な単純化もできるようになります。
-/

example (x y : Nat) : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  -- `simp` だけでは証明が終わらない
  fail_if_success solve
  | simp

  -- 適当に証明する
  grind

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

`simp` は自動的に証明を行ってくれますが、何が行われたのか知りたいときもあります。`simp?` は単純化に何が使われたのかを明示し、`simp only` を用いて書き直すことができるようにしてくれます。-/

/-⋆-//--
info: Try this:
  [apply] simp only [forall_const, imp_self, or_true]
-/
#guard_msgs in --#
example (P : Prop) : (True → P) ∨ (P → P) := by
  simp?

/- ### simp_all
[`simp_all`](./SimpAll.md) はローカルコンテキストとゴールをこれ以上単純化できなくなるまですべて単純化します。-/

example {P Q : Prop} (hP : P) (hQ : Q) : P ∧ (Q ∧ (P → Q)) := by
  -- simp at * は失敗する
  fail_if_success simp at *

  simp_all

/-
[^disch]: このコード例は <https://leanprover-community.github.io/extras/simp.html> における記述を参考にしています。
-/
