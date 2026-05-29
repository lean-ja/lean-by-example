
/-- 何らかの関数 -/
opaque f : Nat → Nat

/-- f は単調増加 -/
axiom f_monotone {a b : Nat} (h : a ≤ b) : f a ≤ f b

section Part1
  /- ## 厳しすぎるパターン指定の例 -/

  grind_pattern f_monotone => f a, f b, f a ≤ f b

  example (a b : Nat) (h : a ≤ b) : f a ≤ f b := by
    -- grind の中の前処理等で `f a ≤ f b` の形が崩れるため、
    -- grind が `f a ≤ f b` のパターンを見つけられない。
    -- そのため grind で証明できない
    fail_if_success grind

    apply f_monotone <;> assumption

end Part1

section Part2
  /- ## ワイルドカードでパターンを緩める例 -/

  grind_pattern f_monotone => f a, f b, f _ ≤ f _

  example (a b : Nat) (h : a ≤ b) : f a ≤ f b := by
    -- grind で証明できるようになった！
    grind

end Part2
