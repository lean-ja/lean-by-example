/- # generalize
`generalize` は，示したい命題を一般化するために使用されます．
-/

variable {n m : Nat}

example : (n + m) ^ 2 + n * (n + m) = n * (n + m) + (n + m) ^ 2 := by
  -- 式の代わりに `x` に置き換えて一般化する
  generalize n * (n + m) = x

  -- `y` に置き換えて一般化する
  generalize (n + m) ^ 2 = y

  -- `y + x = x + y` を示せばよい
  show y + x = x + y

  -- 足し算の可換性から従う
  simp [Nat.add_comm]

/- 単に `generalize e = x` とすると，非可逆的に置換されますが，`generalize h : e = x` とすると置換に使用した命題に後からアクセスできるようになります．-/

example : m ^ 2 + 1 ≥ m ^ 2 := by
  -- 一般化する
  generalize h : m ^ 2 = x

  -- ローカルコンテキストに命題 `h` が追加される
  guard_hyp h : m ^ 2 = x

  simp_arith
