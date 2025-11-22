/-- 整数をイメージした何か -/
opaque MyInt : Type

variable [LE MyInt] [Zero MyInt]

/-- `x ≤ 0` という前提の下では `0 ≤ x` と `x = 0` は同値 -/
@[simp]
axiom MyInt.le_zero_implies {x : MyInt} (le : x ≤ 0) : 0 ≤ x ↔ x = 0

example {x : MyInt} (le : x ≤ 0) (ge : 0 ≤ x) : x = 0 := by
  -- `simp` は「前提条件を満たしたときの書き換え」ができない
  fail_if_success simp at ge

  -- 手動で引数を `by assumption` で与えればできる
  simp [MyInt.le_zero_implies (by assumption)] at ge
  assumption
