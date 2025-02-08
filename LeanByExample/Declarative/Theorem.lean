/-
# theorem
`theorem` は名前付きで命題を証明するためのコマンドです。より正確には、`theorem` は証明項を定義するためのコマンドだといえます。
-/

/-- 自然数に右から0を足しても変わらない -/
theorem add_zero {n : Nat} : n + 0 = n := by simp

-- `add_zero` という項の型が、命題の内容になっている
#check (add_zero : ∀ {n : Nat}, n + 0 = n)

/- ## def との違い
`theorem` コマンドは特定の型を持つ項を定義するという意味で、[`def`](./Def.md) と同じです。実際、`def` を使っても証明項を定義することは可能です。しかし `theorem` を使っても関数などを定義することはできません。`theorem` で宣言できる項は命題のみです。-/

def add_zero' {n : Nat} : n + 0 = n := by simp

/-⋆-//--
error: type of theorem 'frac' is not a proposition
  Nat → Nat
-/
#guard_msgs (whitespace := lax) in --#
theorem frac (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * frac n
