/- # fun_induction

`fun_induction` は、特定の再帰関数用の帰納法ができるようにします。
-/
section --#
variable {α : Type}

/-- リストの順番を逆にする -/
def reverse (as : List α) :=
  match as with
  | [] => []
  | a :: as => reverse as ++ [a]

/-- `reverse`と`(· ++ ·)`は可換 -/
theorem reverse_append (l₁ l₂ : List α)
  : reverse (l₁ ++ l₂) = reverse l₂ ++ reverse l₁ := by
  fun_induction reverse l₁
  case case1 => simp
  case case2 a as ih =>
    dsimp [reverse]
    rw [ih]
    ac_rfl

end --#
/- ## 舞台裏

再帰関数 `foo` を定義すると、裏で Lean が帰納原理(induction principle)`foo.induct`と`foo.induct_unfolding`を生成します。
-/

/-- フィボナッチ数列 -/
def fibonacci (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci (n + 1) + fibonacci n

#check fibonacci.induct

#check fibonacci.induct_unfolding

/- 帰納原理が生成されるのは再帰的な関数のみです。再帰的でない関数には生成されません。-/

def bar : Nat → Nat
  | 0 => 0
  | _ => 1

-- 帰納原理が生成されていない
#check_failure bar.induct

/- `fun_induction` タクティクは、この自動生成された `foo.induct_unfolding` を利用して帰納法を行っています。 -/
