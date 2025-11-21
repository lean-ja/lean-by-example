/- # simp

`simp` は、ターゲットを決められた規則に基づいて自動で単純化（simplify）するタクティクです。

基本的には、`A = B` または `P ↔ Q` という形の補題を登録しておくと、`A` を `B` に、または `P` を `Q` に自動で単純化してくれます。左辺を右辺に書き換え、右辺を左辺に戻すことはないため、右辺は左辺よりも「単純」であることが求められます。等価性に基づいて書き換えるので [`rw`](#{root}/Tactic/Rw.md) タクティクと似ていますが、`rw` と異なり必ずしも明示的に書き換えルールを引数として与える必要がありません。

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

/- ## 等式・同値性以外のルールを登録した場合

等式や同値性以外のルールを登録した場合、等式・同値性への変換が自動的に行われたうえで登録されます。

たとえば下記の例のように、`1 ≠ 0` というルールを `simp` 補題として登録した場合、`(1 = 0) = False` という定理が自動生成されそれに基づいて単純化が行われるようになります。

{{#include ./Simp/OneNeqZero.md}}
-/

/- 一般に等式の形をしているとは限らない命題 `P : Prop` に対して `P` という命題を `simp` 補題として登録すると `P = True` という定理が、`¬ P` という命題を登録すると `P = False` という定理がそれぞれ自動生成されて単純化に使用されます。

{{#include ./Simp/MyEven.md}}
-/

/- ## simp で使用できる構文

### 補題の指定
既知の `h : P` という命題を使って単純化させたいときは、明示的に `simp [h]` と指定することで可能です。複数個指定することもできます。また `simp only [h₁, ... , hₖ]` とすると `h₁, ... , hₖ` だけを使用して単純化を行います。-/

example {P Q : Prop} (h : Q) : (P → P) ∧ Q := by
  simp only [imp_self, true_and]
  assumption

/- 単に名前を定義に展開したい場合は [`dsimp`](./Dsimp.md) を使用します。

### at 構文

`simp` は [at 構文](#{root}/Syntax/AtLocation.md) を受け入れます。`simp` は何も指定しなければゴールを単純化しますが、ローカルコンテキストにある `h : P` を単純化させたければ `simp at h` と指定することで可能です。ゴールと `h` の両方を単純化したいときは `simp at h ⊢` とします。-/

example {n m : Nat} (h : n + 0 + 0 = m) : n = m + (0 * n) := by
  simp only [Nat.add_zero, Nat.zero_mul] at h ⊢
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
  error: Tactic `simp` failed with a nested error:
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

`simp` は自動的に証明を行ってくれますが、何が使われたのか知りたいときもあります。`simp?` は単純化に何が使われたのかを示してくれるので、`simp only` などを用いて明示的に書き直すことができます。-/

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
