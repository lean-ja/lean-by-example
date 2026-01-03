/- # mutual

`mutual` は、相互再帰を定義するために使用されます。

以下は、作為的ではあるものの簡単な例です。
-/
mutual

/-- 偶数であることを表す述語 -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ {n : Nat} (h : Odd n) : Even (n + 1)

/-- 奇数であることを表す述語 -/
inductive Odd : Nat → Prop where
  | succ {n : Nat} (h : Even n) : Odd (n + 1)
end
/-
相互再帰を使って定義された概念に対して証明を行う場合、定理も相互再帰的にする必要が生じることがあります。
-/
mutual

theorem Even.exists {n : Nat} (h : Even n) : ∃ a, n = 2 * a := by
  cases h with
  | zero => exists 0
  | @succ n h =>
    obtain ⟨a, ha⟩ := h.exists
    exists (a + 1)
    grind

theorem Odd.exists {n : Nat} (h : Odd n) : ∃ a, n = 2 * a + 1 := by
  cases h with
  | @succ n h =>
    obtain ⟨a, ha⟩ := Even.exists h
    exists a
    grind

end
