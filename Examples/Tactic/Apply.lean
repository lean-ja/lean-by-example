import Mathlib.Tactic.ApplyAt -- `apply at` のため --#
import Std.Tactic.GuardExpr -- `guard_hyp` のため --#
import Std.Tactic.Replace -- `replace` のため --#
/-! # apply

`apply` は含意 `→` をゴールに適用するタクティクです．
ゴールが `⊢ Q` で，ローカルコンテキストに `h: P → Q` があるときに，`apply h` を実行するとゴールが `⊢ P` に書き換わります．
-/

variable (P Q : Prop)

/-- `P → Q` かつ `P` ならば `Q` -/
example (h: P → Q) (hP: P) : Q := by
  apply h

  -- ゴールが `P` に変わっている
  show P

  exact hP

/-! 注意点として，`h: P → Q` は `P` の証明を受け取って `Q` の証明を返す関数でもあるので，上記の例は `apply` を使わずに `exact h hP` で閉じることもできます．-/

example (h: P → Q) (hP: P) : Q := by
  exact h hP

/-!
## 否定 ¬ について
また，Lean では否定 `¬ P` は `P → False` として実装されているため，ゴールが `⊢ False` であるときに `hn: ¬P` に対して `apply hn` とするとゴールが `⊢ P` に書き換わります． -/

example (hn: ¬ P) (hP: P) : False := by
  apply hn
  show P

  exact hP

/-!
## exact との関連
[exact](./exact.md) の代わりに `apply` を使うことができます．
-/

example (h: P → Q) (hP: P) : Q := by
  apply h hP

/-! ## よくあるエラー

`apply` には引数が必須なのですが，省略しても近くにエラーが出ません．一般に，構文的に間違った証明を書いた場合には，エラーがわかりやすい場所に出てくれる保証はありません．

## apply at

`apply` は通常ゴールに対して適用しますが, `at` を付けてローカルコンテキストの命題などに対して使用するという使い方があります．
この `at` がついている構文は通常の `apply` とは異なり，後方推論ではなく前方推論になります．
また，この構文を使用するには追加で `import` 文が必要です．
-/

example (h : P → Q) (hP : P) : Q := by
  try
    -- `hP` に `h` を適用してしまう
    apply h at hP

    -- `hP` が書き換わる
    guard_hyp hP : Q

    fail

  -- `apply at` は `replace` と同じように動作する
  replace hP := h hP

  -- `hP` が書き換わる
  guard_hyp hP : Q

  assumption
