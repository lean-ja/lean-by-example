/- # trivial

`trivial` は明らかなことを示します．

`trivial` は，`rfl` や `contradiction` などのタクティクを実行して，現在のゴールを閉じようとします． -/
-- 定義から明らかな等式
example : 1 + 1 = 2 := by trivial

-- 矛盾があるので, どんな命題でも証明できる
example (P : Prop) (h: False) : P := by trivial

/-! 普段の数学でいう「自明」な命題は `trivial` では示せないことがほとんどだと思います．[aesop](./Aesop.md) を試してみてください．-/
