/- # replace

`replace` は [`have`](./Have.md) と同じく補題を入手するためのタクティクですが、`have` とは異なりローカルコンテキストにすでにある命題を置き換えることができます。

`have` を使った場合、ローカルコンテキストにすでに `h : P` がある状態で、再び `h` という名前で別の命題を示すと、古い方の `h` はアクセス不能になって `†` が付いた状態になってしまいます。

`replace` であれば、古い方が新しい方に置き換えられ、`†` の付いた命題は出現しません。 -/
import Mathlib.Tactic -- 大雑把に import する

/-- `5 * n` が偶数なら、`n` も偶数 -/
example : ∀ (n : ℤ), Even (5 * n) → Even n := by
  intro n hn

  -- `Even (5 * n)` という仮定を分解
  obtain ⟨k, hk⟩ := hn

  -- 以下がローカルコンテキストに追加される
  guard_hyp hk : 5 * n = k + k

  -- `k + k` という形が使いづらいので、`2 * k` に置き換える
  replace hk : 5 * n = 2 * k := by
    rw [hk]
    ring

  -- `hk` の内容が変化している
  guard_hyp hk : 5 * n = 2 * k

  -- 計算をする
  have : n = 2 * (k - 2 * n) := calc
    _ = 5 * n - 4 * n := by ring
    _ = 2 * k - 4 * n := by rw [hk]
    _ = 2 * (k - 2 * n) := by ring

  exists k - 2 * n
  nth_rw 1 [this]
  ring
