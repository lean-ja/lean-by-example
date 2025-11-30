
/-- 何らかの関数 -/
opaque f : Nat → Nat

/-- `f` は単調増加関数 -/
axiom f_monotone {a b : Nat} (h : a ≤ b) : f a ≤ f b

section

  -- 多くのパターンを指定してインスタンス化ルールを設定
  local grind_pattern f_monotone => f a, f b, a ≤ b

  example (a : Nat) (h1 : a ≤ 1) (h2 : f 2 = 10) : f a ≤ 10 := by
    -- 最初は示すことができない
    fail_if_success grind

    -- `a ≤ 2` であることを明示的に教えると通るようになる。
    -- `f_monotone` のインスタンス化パターンが満たされるからだと考えられる。
    have : a ≤ 2 := by grind
    grind

end

-- インスタンス化の条件を緩めると、`grind` 一発で通るようになる
grind_pattern f_monotone => f a, f b

example (a : Nat) (h1 : a ≤ 1) (h2 : f 2 = 10) : f a ≤ 10 := by
  grind
