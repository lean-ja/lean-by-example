-- 定義から明らかな等式
example : 1 + 1 = 2 := by trivial

-- 矛盾があるので, どんな命題でも証明できる
example (h: False) : P := by trivial