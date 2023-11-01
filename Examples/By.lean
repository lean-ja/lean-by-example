import Std.Tactic.ShowTerm -- `by?` を使用するのに必要

/-! ## 項による証明 -/

-- `P → R` というのは `P` の証明を与えられたときに `R` の証明を返す関数の型
-- したがって，その証明は関数となる
example (hPQ : P → Q) (hQR : Q → R) : P → R :=
  fun hP ↦ hQR (hPQ hP)

/-! ## タクティクによる証明 -/

-- 同じ命題をタクティクで示した例
example (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  exact hQR (hPQ hP)

/-!
  ## by?

  `by?` を使うとタクティクモードで構成した証明を直接構成した証明に変換してくれます．
-/

example (hPQ : P → Q) (hQR : Q → R) : P → R := by?
  -- `Try this: fun hP => hQR (hPQ hP)` と提案してくれる
  intro hP
  exact hQR (hPQ hP)
