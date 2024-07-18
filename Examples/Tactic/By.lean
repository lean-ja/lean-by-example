/- # by

Lean においては、命題は型で、証明はその項です。命題 `P` の証明を構成するとは項 `h : P` を構成するということです。`by` は、証明の構成をタクティクで行いたいときに使います。-/

/-! 証明項による証明とは、たとえば次のようなものです。 -/

variable (P Q R : Prop)

-- `P → R` というのは `P` の証明を与えられたときに `R` の証明を返す関数の型
-- したがって、その証明は関数となる
example (hPQ : P → Q) (hQR : Q → R) : P → R :=
  fun hP ↦ hQR (hPQ hP)

/-! 同じ命題をタクティクを使って示すと、例えば次のようになります。 -/

-- 同じ命題をタクティクで示した例
example (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  exact hQR (hPQ hP)

/-! ## by?

`by` の代わりに `by?` を使うとタクティクモードで構成した証明を直接構成した証明に変換してくれます。`show_term by` としてもほぼ同じ結果が得られます。
-/

example (hPQ : P → Q) (hQR : Q → R) : P → R := by?
  -- `Try this: fun hP => hQR (hPQ hP)` と提案してくれる
  intro hP
  exact hQR (hPQ hP)

/-- info: Try this: fun hP => hQR (hPQ hP) -/
#guard_msgs in
example (hPQ : P → Q) (hQR : Q → R) : P → R := show_term by
  intro hP
  exact hQR (hPQ hP)
