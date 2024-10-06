/- # clear

Lean で複雑な証明を書いていると、ローカルコンテキストに今まで導入した定義や示した補題が溜まってきて見づらくなることがあります。そうしたとき、`clear` タクティクを使うと指定した項を削除したり、指定した項以外を削除したりといったことができます。-/
import Mathlib.Tactic.ClearExcept -- `clear` タクティクで「～以外」を指定できるようにする

-- 未使用の変数に対する警告をオフにする
set_option linter.unusedVariables false

variable (P Q R : Prop)

example (hP : P) (hQ : Q) (hR : R) : R := by
  -- `hP` と `hR` 以外をローカルコンテキストから削除する
  clear * - hR hP

  -- `hP` も削除する
  clear hP

  exact hR

/- ローカルコンテキストが複雑で見づらいときに、`clear` で関係があるもの以外を削除して見やすくするといった使い方ができます。-/
