/- # rw

`rw` は rewrite（書き換え）を行うタクティクです。等式や同値関係をもとに書き換えを行います。

`hab : a = b` や `hPQ : P ↔ Q` がローカルコンテキストにあるとき、

* `rw [hab]` はゴールの中の `a` をすべて `b` に置き換え、
* `rw [hPQ]` はゴールの中の `P` をすべて `Q` に置き換えます。

順番は重要で、`b` を `a` に置き換えたいときなどは `rw [← hab]` のように `←` をつけます。-/

variable {a b c d e f : Nat}

example (h : a = b) (hb : a + 3 = 0) : b + 3 = 0 := by
  -- `rw [h]` だと `a` を `b` に置き換えるという意味になり、失敗する
  fail_if_success rw [h]

  -- `←` をつけて逆向きにすれば通る
  rw [← h]

  assumption

-- 同値関係に基づいて書き換えを行う例
example (P Q : Prop) (h : P ↔ P ∧ Q) : P → Q := by
  intro (hP : P)
  rw [h] at hP

  -- `P ↔ P ∧ Q` で書き換えを行ったので、
  -- `P` が `P ∧ Q` に置き換わった
  guard_hyp hP : P ∧ Q

  exact hP.right

/- `h1, h2, ...` について続けて置き換えを行いたいときは、`rw [h1, h2, ...]` のようにします。

ゴールではなく、ローカルコンテキストにある `h : P` を書き換えたいときには `at` をつけて `rw [hPQ] at h` とします。すべての箇所で置き換えたいときは `rw [hPQ] at *` とします。

また、ゴールとローカルコンテキストの仮定 `h` に対して同時に書き換えたいときは `⊢` 記号を使って `rw [hPQ] at h ⊢` のようにします。-/

example (h : a * b = c * d) (h' : e = f + 0) : a * (b * e + 0) = c * (d * f) := by
  -- ゴールとローカルコンテキストの両方に対して書き換えを行う
  rw [Nat.add_zero] at h' ⊢

  rw [h']

  -- 結合法則を使う
  rw [← Nat.mul_assoc, h]

  -- 結合法則を使う
  rw [Nat.mul_assoc]

/-! ## nth_rw

`rw` はマッチした項をすべて置き換えてしまいます。
特定の項だけを書き換えたいとき、[`nth_rw`](./NthRw.md) が使用できます.

## rewrite

`rewrite` というタクティクもあります。`rw` とよく似ていて、違いは `rw` が書き換え後に自動的に `rfl` を実行するのに対して、`rewrite` は行わないということです。`rewrite` はユーザにとっては `rw` の下位互換なので、あまり使うことはないかもしれません。-/

example (h : a = b) : a = b := by
  try
    -- `rw` を使用した場合は一発で証明が終わる
    rw [h]
    done

    fail

  rewrite [h]

  -- ゴールを `b = b` にするところまでしかやってくれない
  show b = b

  rfl
