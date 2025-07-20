/- # induction

`induction` は、帰納法のためのタクティクです。自然数 [`Nat`](#{root}/Type/Nat.md) や連結リスト [`List`](#{root}/Type/List.md) など、帰納的に定義されたものに対して何か証明しようとしているとき、帰納法を使うことが自然な選択になります。

典型的な例は、自然数に対する数学的帰納法です。前提として、ある述語 `P : Nat → Prop` に対して `∀ n, P n` を示そうとしているとします。このとき、以下を示せば十分であるというのが、数学的帰納法の主張です。

* `P 0` が成り立つ。
* `∀ n, P n → P (n + 1)` が成り立つ。
-/
import Mathlib.Tactic.Ring -- `ring` を使うため --#

/-- `0` から `n` までの和を計算する関数 -/
def sum (n : Nat) : Rat :=
  match n with
  | 0 => 0
  | n + 1 => (n + 1) + sum n

example (n : Nat) : sum n = n * (n + 1) / 2 := by
  -- `n` についての帰納法で示す
  induction n with

  -- `n = 0` の場合
  | zero => simp [sum]

  -- `0` から `n` までの自然数で成り立つと仮定する
  | succ n ih =>
    -- 帰納法の仮定が手に入る
    guard_hyp ih : sum n = n * (n + 1) / 2

    -- `sum` の定義を展開し、帰納法の仮定を適用する
    simp [sum, ih]

    -- 後は可換環の性質から示せる
    ring

/- なお、`=>` は省略することができます。 -/

example (n : Nat) : sum n = n * (n + 1) / 2 := by
  induction n with | zero | succ n ih
  · simp [sum]
  · simp [sum, ih]
    ring

/- また `induction .. with` の直後にタクティクを書くと、そのタクティクをすべてのゴールに対して適用します。 -/

example (n : Nat) : sum n = n * (n + 1) / 2 := by
  induction n with simp [sum]
  | succ n ih =>
    simp [ih]
    ring

/- ## 帰納法の対象

実際には帰納法は自然数の専売特許ではありません。[`inductive`](#{root}/Declarative/Inductive.md) コマンドで定義されたものであれば、帰納法を使うことができます。-/

/-- 標準ライブラリの定義を真似て構成した順序関係 -/
inductive Nat.myle (n : Nat) : Nat → Prop where
  /-- 常に `n ≤ n` が成り立つ -/
  | refl : myle n n

  /-- `n ≤ m` ならば `n ≤ m + 1` が成り立つ -/
  | step {m : Nat} : myle n m → myle n (m + 1)

@[inherit_doc] infix:50 " ≤ₘ " => Nat.myle

-- 順序関係について帰納法を回して証明をする例
example {m n k : Nat} (h₁ : m ≤ₘ n) (h₂ : n ≤ₘ k) : m ≤ₘ k := by
  induction h₂ with
  | refl => assumption
  | @step l h₂ ih =>
    apply Nat.myle.step (by assumption)

/- ## generalizing 構文

時として、帰納法の仮定が弱すぎることがあります。
-/

/-- 階乗関数 -/
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

/-- 階乗関数の末尾再帰バージョン -/
@[grind]
def factorialTR (n : Nat) : Nat :=
  aux n 1
where
  @[grind] aux (n acc : Nat) :=
    match n with
    | 0 => acc
    | n + 1 => aux n (acc * (n + 1))

set_option warn.sorry false in --#
example (n acc : Nat) : factorialTR.aux n acc = acc * factorialTR.aux n 1 := by
  induction n with
  | zero => simp [factorialTR.aux]
  | succ n ih =>
    dsimp [factorialTR.aux]

    -- 得られている帰納法の仮定では `.aux` の2つめの引数は `acc` だが
    guard_hyp ih : factorialTR.aux n acc = acc * factorialTR.aux n 1

    -- これは示すべきことに合致しないので使えない。
    guard_target = factorialTR.aux n (acc * (n + 1)) = acc * factorialTR.aux n (1 * (n + 1))

    sorry

/- `generalizing` 構文で帰納法の仮定の中の特定の変数を一般化することができて、そうすると証明が通るようになることがあります。 -/

example (n acc : Nat) : factorialTR.aux n acc = acc * factorialTR.aux n 1 := by
  induction n generalizing acc with
  | zero => simp [factorialTR.aux]
  | succ n ih =>
    dsimp [factorialTR.aux]

    -- 帰納法の仮定が強くなっている！！
    guard_hyp ih : ∀ (acc : ℕ), factorialTR.aux n acc = acc * factorialTR.aux n 1

    grind

/- ただし注意点として、`induction .. generalizing` 構文を実行するとき、帰納法を行う変数が一般化される変数に依存していてはいけないというルールがあります。-/

/-⋆-//-- error: Variable 'm' cannot be generalized because the induction target depends on it -/
#guard_msgs in --#
example {n m : Nat} (h : Even (n + m)) (hm : Even m) : Even n := by
  induction hm generalizing m

/-
## 完全帰納法

時には、より強い帰納法が必要なこともあります。 強い帰納法とは、 たとえば以下のような形式で表されるような帰納法のことです。

* `∀ n, (∀ k < n, P (k)) → P (n)` を示す。
* したがって `∀ n, P (n)` である。

これは超限帰納法の特別な場合で、完全帰納法や累積帰納法とも呼ばれます。
自然数の場合は、`Nat.strong_induction_on` を `using` キーワードに渡せば使うことができます。
-/

/-- 素数であるという命題 -/
@[simp]
def IsPrime (n : Nat) := 1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

@[grind ->]
theorem IsPrime_pos (n : Nat) (h : IsPrime n) : 1 < n := by
  simp_all

/-- 1より大きい任意の数は素因数を持つ -/
theorem exists_prime_factor (n : Nat) (hgt : 1 < n) :
  ∃ k, IsPrime k ∧ k ∣ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    -- nが素数であるかどうかによって場合分けをする。
    by_cases hprime : IsPrime n
    case pos =>
      -- nが素数であるときは明らか。
      grind [Nat.dvd_refl]

    -- 以下、nは素数でないとする。
    -- nは素数ではないのでnより真に小さい約数を持つ。
    have ⟨k, _, _, _⟩ : ∃ k, 1 < k ∧ k < n ∧ k ∣ n := by
      simp_all

    -- 帰納的に、k には素因数が存在するとしてよい。
    have := ih k ‹k < n›

    -- k ∣ n なので、k に素因数があるなら n にも存在する。
    grind [Nat.dvd_trans]

/- ## よくあるエラー
`induction` タクティクを使ったときに、`index in target's type is not a variable` というエラーが出ることがあります。
-/

/-- 偶数であることを表す帰納的述語 -/
inductive MyEven : Nat → Prop where
  | zero : MyEven 0
  | succ : {n : Nat} → MyEven n → MyEven (n + 2)

/-⋆-//--
error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  0
-/
#guard_msgs in --#
example (h : MyEven 0) : True := by
  induction h

/- これは型族の添え字が変数ではないから起こることです。その証拠に、変数にするとエラーにならなくなります。-/

example (n m : Nat) (h : MyEven (n + m)) : True := by
  generalize n + m = x at h
  induction h
  · trivial
  · trivial

/- ## 再帰的定理
Lean では、実は帰納法を使用するのに必ずしも `induction` は必要ありません。場合分けの中で示されたケースを帰納法の仮定として使うことができます。これは recursive theorem(再帰的定理) と呼ばれることがあります。[^recursive]
-/

theorem sum_exp (n : Nat) : sum n = n * (n + 1) / 2 := by
  match n with

  -- `n = 0` の場合
  | 0 => simp [sum]

  -- `0` から `n` までの自然数で成り立つと仮定する
  | n + 1 =>
    -- 仮定から、`n` について成り立つ
    have ih := sum_exp n

    -- 仮定を適用して展開する
    simp [sum, ih]

    -- 後は可換環の性質から示せる
    ring

/- `have` で宣言された命題の証明の中では、この方法は使用できません。-/
set_option warn.sorry false in --#

theorem sample : True := by
  have h : ∀ n, sum n = n * (n + 1) / 2 := by
    intro n
    match n with
    | 0 => simp [sum]
    | n + 1 =>
      -- h 自身を参照することができない
      fail_if_success have ih := h n
      sorry
  trivial

/-
[^recursive]: [lean公式ブログの Functional induction についての記事](https://lean-lang.org/blog/2024-5-17-functional-induction/) で recursive theorem という言葉が使われています。
-/
