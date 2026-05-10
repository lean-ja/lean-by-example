
-- 整数全体を表す記号
notation:max "ℤ" => Int

/-- 絶対値。値は整数(自然数ではない) -/
def Int.abs (a : ℤ) : ℤ := max a (- a)

@[inherit_doc]
notation:max "|" a "|" => Int.abs a

/-- 0 以上の数については、絶対値は元の数に等しい -/
theorem Int.abs_of_nonneg {a : ℤ} (ha : 0 ≤ a) : |a| = a := by
  grind only [abs, = Int.max_def]

section
  -- `0 ≤ a` を探索パターンとして登録してみると
  local grind_pattern Int.abs_of_nonneg => |a|, 0 ≤ a

  -- 何故か `ha : 0 ≤ a` という仮定を見つけてくれず、
  -- `grind` で証明できない。
  set_option warn.sorry false in --#
  example {a : ℤ} (ha : 0 ≤ a) : |a| = a := by
    fail_if_success grind
    sorry
end

-- `guard` 制約としていれてやると上手く動作する
grind_pattern Int.abs_of_nonneg => |a| where
  guard 0 ≤ a

example {a : ℤ} (ha : 0 ≤ a) : |a| = a := by
  grind
