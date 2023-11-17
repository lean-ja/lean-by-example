import Mathlib.Tactic.Ring -- `ring` のために必要

variable (x y : ℤ)

/-! ## ring -/

example : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

/-!
  ## 環でないものに ring を使ったら

  自然数 `ℕ` は環ではありません．
  そのため，`ring` を使うと代わりに `ring_nf` を使うように促されます．
-/

-- なお，Lean では自然数の引き算は
-- `n ≤ m` のとき `n - m = 0` になるように定義されています
#guard 7 - 42 = 0

-- 整数にすると結果が変わります
#guard 7 - (42 : ℤ) = - 35

variable (n : ℕ)

example : n - n + n = n := by
  -- `Try this: ring_nf` と言われる
  try ring

  -- 代わりに `ring_nf` を使ってもこの場合は効果なし
  ring_nf

  show n - n + n = n
  simp

/-!
  ## ring の中身を見る方法

  `simp` 等と異なり，`ring?` タクティクは用意されていませんが，
  `show_term` で具体的にどんなルールが適用されたのかを知ることができます．
  ただし，その出力結果は非常に長く読みづらいものであることがしばしばです．
-/

example : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by

  /-
    以下のような出力が100行以上続く
    Try this: exact Mathlib.Tactic.Ring.of_eq
    (Mathlib.Tactic.Ring.pow_congr
      ...
  -/
  show_term ring
