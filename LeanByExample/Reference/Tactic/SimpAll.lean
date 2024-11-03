/- # simp_all

`simp_all` タクティクは、`simp` タクティクの派生で、仮定とゴールに対してこれ以上適用できなくなるまで `simp` を適用します。

`simp at *` と似ていますが、`simp_all` は簡約された仮定を再び簡約に使うなど再帰的な挙動をします。
-/

example (P : Nat → Bool)
    (h1 : P (if 0 + 0 = 0 then 1 else 2))
    (h2 : P (if P 1 then 0 else 1) ) : P 0 := by
  simp at *

  -- まだゴールが残っている
  show P 0

  simp [h1] at h2
  assumption

example (P : Nat → Bool)
    (h1 : P (if 0 + 0 = 0 then 1 else 2))
    (h2 : P (if P 1 then 0 else 1) ) : P 0 := by
  -- 一発で終わる。
  -- h1 を簡約した後で、h2 を「簡約後の h1」を使って簡約し、
  -- ゴールと仮定が一致していることを確認するという挙動をする。
  simp_all
