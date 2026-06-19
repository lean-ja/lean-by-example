import Lean.LibrarySuggestions.Default

/--
Lean リポジトリの `tests/elab/library_suggestions_persistent.lean` で使われている例。
`Dyadic.roundDown_le` などの補題は `grind` だけでは見つけられないが、
`grind +suggestions` は premise selection によって関連する補題を見つける。
-/
example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
  fail_if_success grind -- grind だけでは証明できない
  grind +suggestions

example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
  grind only [Dyadic.roundDown_le]
