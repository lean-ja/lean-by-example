/- # assumption

`assumption` は、現在のゴール `⊢ P` がローカルコンテキストにあるとき、ゴールを閉じます。-/

variable (P Q : Prop)

example (hP: P) (_: Q) : P := by
  assumption

/- `assumption` による証明は、どの仮定を使うか明示すれば [`exact`](./Exact.md) で書き直すことができます。`assumption` を使用することにより、仮定の名前の変更に対してロバストになるほか、意図がわかりやすくなるというメリットがあります。-/

example (hP: P) (_: Q) : P := by
  exact hP

/- ## 補足

なお、シングル山括弧 `‹›` を使って `‹P›` と書くと、「命題 `P` の証明を `by assumption` で埋めてください」と Lean に指示したことになります。-/

example (P Q R : Prop) (hp : P) (hq : Q) (h : P → Q → R) : R := by
  exact h ‹P› ‹Q›
