-- `by?` を使用するのに必要
import Std.Tactic.ShowTerm

-- ANCHOR: first
-- `P → R` というのは `P` の証明を与えられたときに `R` の証明を返す関数の型
-- したがって，その証明は関数となる
example (hPQ : P → Q) (hQR : Q → R) : P → R :=
  fun hP ↦ hQR (hPQ hP)


-- 同じ命題をタクティクで示した例
example (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  exact hQR (hPQ hP)
-- ANCHOR_END: first


-- ANCHOR: question
example (hPQ : P → Q) (hQR : Q → R) : P → R := by?
  -- `Try this: fun hP => hQR (hPQ hP)` と提案してくれる
  intro hP
  exact hQR (hPQ hP)
-- ANCHOR_END: question