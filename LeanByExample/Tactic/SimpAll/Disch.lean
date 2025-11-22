/-- 整数をイメージした何か -/
opaque MyInt : Type

variable [LE MyInt] [Zero MyInt]

/-- `x ≤ 0` という前提の下では `0 ≤ x` と `x = 0` は同値 -/
@[simp]
axiom MyInt.le_zero_implies {x : MyInt} (le : x ≤ 0) : 0 ≤ x ↔ x = 0

example (x : MyInt) (le : x ≤ 0) (ge : 0 ≤ x) : x = 0 := by
  -- `simp at *` は「前提条件を満たしたときの書き換え」ができない
  fail_if_success simp at *

  -- discharger の指定が必要
  simp (disch := assumption) at *
  assumption

example (x : MyInt) (le : x ≤ 0) (ge : 0 ≤ x) : x = 0 := by
  -- `simp_all` はローカルコンテキストを自動で引数に拾ってくれる
  simp_all only [MyInt.le_zero_implies]
