import Mathlib.Algebra.Parity -- `Even` のために必要
import Mathlib.Tactic.NthRewrite -- `nth_rw` のために必要
import Mathlib.Tactic.Ring -- `ring` のために必要

/-- `5 * n` が偶数なら，`n` も偶数 -/
example : ∀ (n : ℤ), Even (5 * n) → Even n := by
  intro n hn

  -- `Even (5 * n)` という仮定を分解
  obtain ⟨ k, hk ⟩ := hn

  -- 以下がローカルコンテキストに追加される
  guard_hyp hk : 5 * n = k + k

  -- `k + k` という形が使いづらいので，`2 * k` に置き換える
  replace hk : 5 * n = 2 * k := by
    rw [hk]
    ring

  -- `hk` の内容が変化している
  guard_hyp hk : 5 * n = 2 * k

  -- 計算をする
  have := calc
    n = 5 * n - 4 * n := by ring
    _ = 2 * k - 4 * n := by rw [hk]
    _ = 2 * (k - 2 * n) := by ring

  exists k - 2 * n
  nth_rw 1 [this]
  ring
