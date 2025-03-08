/- # simp

`simp` は、ターゲットを決められた規則に基づいて自動で単純化（simplify）するタクティクです。`[simp]` 属性を付けることにより単純化に使ってほしい命題を登録することができます。-/
import Mathlib.Tactic.Ring -- `ring` を使うため --#
import Mathlib.Tactic.Says -- `says` を使うために必要 --#
import Mathlib.Tactic.Tauto -- `tauto` を使うため

set_option linter.flexible false in --#

example {P Q R : Prop} : (P ∨ Q ∨ R) ∧ R ↔ R := by
  -- simp だけでは証明が終わらない
  simp
  show R → P ∨ Q ∨ R

  -- 残りを適当に証明する
  intro hR
  tauto

@[simp]
theorem or_and {P Q R : Prop} : (P ∨ Q ∨ R) ∧ R ↔ R := by
  constructor

  -- 左から右を示す
  case mp =>
    intro ⟨_, hR⟩
    assumption

  -- 右から左を示す
  case mpr =>
    -- R が成り立つと仮定する
    intro hR

    -- R は成り立つので、後は P ∨ Q ∨ R が成り立つことを示せばよい
    refine ⟨?_, hR⟩

    -- R が成り立つことから明らか。
    tauto

-- 一度登録した命題は `simp` で示せるようになる。
example {P Q R : Prop} : (P ∨ Q ∨ R) ∧ R ↔ R := by simp

/- なお、`[simp]` 属性を付与した命題は「左辺を右辺に」単純化するルールとして登録されます。
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
/- ## simp で使用できる構文

### 補題の指定
既知の `h : P` という命題を使って単純化させたいときは、明示的に `simp [h]` と指定することで可能です。複数個指定することもできます。また `simp only [h₁, ... , hₖ]` とすると `h₁, ... , hₖ` だけを使用して単純化を行います。-/

example {P Q R : Prop} (h : R) : (P ∨ Q ∨ R) ∧ R := by
  simp only [or_and]
  assumption

/- 単に名前を定義に展開したい場合は [`dsimp`](./Dsimp.md) を使用します。

### at 構文

`simp` は [at 構文](#{root}/Parser/AtLocation.md) を受け入れます。`simp` は何も指定しなければゴールを単純化しますが、ローカルコンテキストにある `h : P` を単純化させたければ `simp at h` と指定することで可能です。ゴールと `h` の両方を単純化したいときは `simp at h ⊢` とします。-/

example {n m : Nat} (h : n + 0 + 0 = m) : n = m + (0 * n) := by
  simp only [add_zero, zero_mul] at h ⊢
  assumption

/- ローカルコンテキストとゴールをまとめて全部単純化したい場合は `simp at *` とします。 -/

/- ## arith オプション
`simp` の設定で `arith` を有効にすると、算術的な単純化もできるようになります。
-/
set_option linter.flexible false in --#

example {x y : Nat} : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
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

example {P Q R : Prop} (h : R) : (P ∨ Q ∨ R) ∧ R := by
  simpa only [or_and]

example {n m : Nat} (h : n + 0 + 0 = m) : n = m := by
  simpa using h

/- ### simp?

`simp` は自動的に証明を行ってくれますが、何が使われたのか知りたいときもあります。`simp?` は単純化に何が使われたのかを示してくれるので、`simp only` などを用いて明示的に書き直すことができます。-/

example {P Q R : Prop} : (P ∨ Q ∨ R) ∧ R ↔ R := by
  simp? says
    simp only [or_and]

/- ### simp_all
[`simp_all`](./SimpAll.md) はローカルコンテキストとゴールをこれ以上単純化できなくなるまですべて単純化します。-/

example {P Q : Prop} (hP : P) (hQ : Q) : P ∧ (Q ∧ (P → Q)) := by
  -- simp at * は失敗する
  fail_if_success simp at *

  simp_all
