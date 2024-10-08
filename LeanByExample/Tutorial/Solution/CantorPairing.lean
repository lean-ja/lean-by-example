/- # Cantor の対関数とその全単射性

## はじめに

有限集合 `A` と `B` に対して、`A` と `B` の要素数が等しいということは、`|A| = |B| = n` となる自然数 `n` が存在するということと同値です。無限集合 `X` に対しては `|X| = n` となる自然数 `n` は存在しないので、一見すると集合の要素数という概念は無限集合には拡張できないように思えます。

しかし、`A` と `B` の要素数が等しいということは、「`A` と `B` の間の一対一で漏れのない対応が存在する」ということとも同値です。この定義は `A` と `B` が無限集合であっても意味をなすので、この解釈をつかって集合の要素数が等しいという概念を無限集合にも拡張することができます。

だいたいこのようにして一般の集合に拡張された「要素の個数」という概念を、濃度と呼びます。

無限集合の濃度に関しては、様々な興味深い事実が知られています。この演習問題では、自然数 `ℕ` とその直積 `ℕ × ℕ` の濃度が等しいということを Mathlib を使いながら示していきます。[^note]

## 問1: sum 関数

まず後で使うために `0` から `n` までの自然数の和を計算する関数 `sum` を定義します。演習として、以下の `sorry` を埋めてみてください。
-/
import Mathlib.Tactic
set_option autoImplicit false --#
set_option relaxedAutoImplicit false --#

/-- `0` から `n` までの自然数の和 -/
def sum (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => (n + 1) + sum n

/-- `sum n = 0` となることと `n = 0` は同値 -/
@[simp] theorem sum_zero_iff_zero {n : ℕ} : sum n = 0 ↔ n = 0 := by
  -- sorry
  cases n <;> simp_all [sum]
  -- sorry

/- ## 対関数とその逆関数
上記で定義した `sum` を使いつつ、Cantor の対関数 `pair` とその逆関数 `unpair` を定義します。座標平面の中心からスタートして、折れ曲がりながら右上に向かうような動きをイメージするとわかりやすいかもしれません。
-/

/-- Cantor の対関数 -/
def pair : ℕ × ℕ → ℕ
  | (m, n) => sum (m + n) + m

@[simp] theorem pair_zero : pair 0 = 0 := by rfl

/-- カントールの対関数の逆関数 -/
def unpair : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | x + 1 =>
    let (m, n) := unpair x
    if n = 0 then (0, m + 1)
    else (m + 1, n - 1)

@[simp] theorem unpair_zero : unpair 0 = 0 := by rfl

/- ## 問2: pair の全射性
では `pair` が全射であることを示してみましょう。`pair ∘ unpair = id` が成り立つことを示せば十分です。以下の `sorry` の部分を埋めて証明を完成させてください。
-/

/-- `pair ∘ unpair = id` が成り立つ。特に `pair` は全射。-/
theorem pair_unpair_eq_id (x : ℕ) : pair (unpair x) = x := by
  -- `x` に対する帰納法を使う
  induction' x with x ih

  -- `x = 0` の場合は明らか
  case zero => /- sorry -/ simp

  -- `x` まで成り立つと仮定して `x + 1` でも成り立つことを示そう。
  case succ =>
    -- まず `unpair` の定義を展開する。
    dsimp [unpair]
    split_ifs

    -- 見やすさのために `(m, n) := unpair x` とおく．
    all_goals
      set m := (unpair x).fst with mh
      set n := (unpair x).snd with nh

    -- `n = 0` の場合
    case pos h =>
      -- `pair (0, m + 1) = x + 1` を示せばよい。
      show pair (0, m + 1) = x + 1

      -- `pair` の定義を展開して、示すべきことを `sum` を使って書き直すと
      -- `sum (m + 1) = x + 1` を示せば良いことが分かる。
      suffices sum (m + 1) = x + 1 from by
        -- sorry
        simpa [pair]
        -- sorry

      -- 帰納法の仮定の主張に対しても、
      -- `pair` から `sum` に書き換えることができて、
      -- `sum m + m = x` であることが分かる。
      replace ih : sum m + m = x := by
        -- sorry
        simpa [pair, ←mh, ←nh, h] using ih
        -- sorry

      -- 後は `sum` の定義から明らか。
      -- sorry
      dsimp [sum]
      omega
      -- sorry

    -- `n ≠ 0` の場合
    case neg h =>
      -- `pair (m + 1, n - 1) = x + 1` を示せばよい。
      show pair (m + 1, n - 1) = x + 1

      -- `pair` の定義を展開して、示すべきことを `sum` を使って書き直すと
      -- `sum (m + n) + m = x` を示せば良いことが分かる。
      suffices sum (m + n) + m = x from by
        -- sorry
        simp only [pair]
        rw [show m + 1 + (n - 1) = m + n from by omega]
        omega
        -- sorry

      -- 帰納法の仮定の主張に対しても、
      -- `pair` から `sum` に書き換えることができて、
      -- `sum (m + n) + m = x` が成り立つことが分かる。
      replace ih : sum (m + n) + m = x := by
        -- sorry
        simpa [pair, unpair, ← mh, ← nh] using ih
        -- sorry

      -- 従って示すべきことが言えた。
      assumption

/- ## 問3: 対関数の単射性
最後に `pair` が単射であることを示してみましょう。`unpair ∘ pair = id` が成り立つことを示せば十分です。以下の `sorry` の部分を埋めて証明を完成させてください。
-/

/-- `unpair ∘ pair = id` が成り立つ。特に `pair` は単射。-/
theorem unpair_pair_eq_id (m n : ℕ) : unpair (pair (m, n)) = (m, n) := by
  -- `x = pair (m, n)` として `x` に対する帰納法を利用する
  induction' h : pair (m, n) with x ih generalizing m n

  -- `pair (m, n) = 0` のときは
  -- `pair` の定義から明らか。
  case zero => /- sorry -/ simp_all [pair]

  -- `pair (m, n) = x + 1` のとき
  case succ =>
    -- `m` がゼロかそうでないかで場合分けする
    match m with

    -- `m = 0` のとき
    | 0 =>
      -- `pair (0, n) = x + 1` により `n > 0` が成り立つ。
      have npos : n > 0 := by
        -- sorry
        rw [show n > 0 ↔ n ≠ 0 from Nat.pos_iff_ne_zero]
        aesop
        -- sorry

      -- よって `sum n = sum (n - 1) + n` と書くことができて、
      have lem : sum n = sum (n - 1) + n := by
        -- sorry
        nth_rw 1 [show n = (n - 1) + 1 from by omega]
        dsimp only [sum]
        omega
        -- sorry

      -- `pair (n - 1, 0) = x` が結論できる。
      have : pair (n - 1, 0) = x := by
        -- sorry
        simp_all [pair]
        omega
        -- sorry

      -- 後は帰納法の仮定から従う。
      -- sorry
      specialize ih (n-1) 0 this
      simp [unpair, ih]
      omega
      -- sorry

    -- `m = m' + 1` のとき
    | m' + 1 =>
      -- `pair` の定義から `pair (m', n + 1) = x` が成り立つ。
      have : pair (m', n + 1) = x := by
        -- sorry
        dsimp [pair] at h ⊢
        rw [show m' + 1 + n = m' + (n + 1) from by ac_rfl] at h
        omega
        -- sorry

      -- 後は帰納法の仮定から従う。
      -- sorry
      specialize ih m' (n + 1) this
      simp [unpair, ih]
      -- sorry

/- [^note]: 本項での証明を書くにあたって [Cantor の対関数の全単射性の証明](http://iso.2022.jp/math/pairing_function.pdf) を参考にいたしました。 -/
