/- # fun_induction

`fun_induction` は、特定の再帰関数用の帰納法ができるようにします。

たとえば、自然数について帰納法を行うと `n = 0` の場合と `n = n' + 1` の場合に場合分けをすることになります。しかし、関数 `f` について何かを示そうとしているとき、`f` が自然数の再帰的構造に沿って定義されているとは限りません。そのような場合に `fun_induction` を使うと、場合分けの枝が一致しない問題と格闘しないで済みます。
-/

/-- フィボナッチ数列の通常の定義をそのまま Lean の関数として書いたもの -/
@[simp]
def fibonacci (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci n + fibonacci (n + 1)

/-- フィボナッチ数列の線形時間の実装 -/
def fib (n : Nat) : Nat :=
  (loop n).1
where
  loop : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
    let p := loop n
    (p.2, p.1 + p.2)

@[simp]
theorem fib_zero : fib 0 = 0 := by rfl

@[simp]
theorem fib_one : fib 1 = 1 := by rfl

/-- `fib` が `fibonacci` と同じ漸化式を満たす -/
@[simp]
theorem fib_add (n : Nat) : fib n + fib (n + 1) = fib (n + 2) := by rfl

/-- `fibonacci` と `fib` は同じ結果を返す -/
example (n : Nat) : fibonacci n = fib n := by
  fun_induction fibonacci n with
  | case1 => rfl
  | case2 => simp
  | case3 n ih1 ih2 =>
    simp [ih1, ih2]

/- [`induction`](#{root}/Tactic/Induction.md) タクティクと同様に、`with` の後にタクティクを続けると、すべての枝に対してそのタクティクを適用します。-/

example (n : Nat) : fibonacci n = fib n := by
  fun_induction fibonacci n with simp_all

/- ## 舞台裏

再帰関数 `foo` を定義すると、裏で Lean が帰納原理(induction principle) `foo.induct` と `foo.induct_unfolding` を生成します。
-/
namespace Hidden --#

/-- フィボナッチ数列 -/
def fibonacci (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci (n + 1) + fibonacci n

#check fibonacci.induct

#check fibonacci.induct_unfolding

end Hidden --#
/- 帰納原理が生成されるのは再帰的な関数のみです。再帰的でない関数には生成されません。-/

def bar : Nat → Nat
  | 0 => 0
  | _ => 1

-- 帰納原理が生成されていない
#check_failure bar.induct

/- `fun_induction` タクティクは、この自動生成された `foo.induct_unfolding` を利用して帰納法を行っています。 -/
