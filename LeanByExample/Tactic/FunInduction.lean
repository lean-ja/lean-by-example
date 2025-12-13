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
  loop (x : Nat) : Nat × Nat :=
    match x with
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

def swapHead (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: y :: xs => y :: x :: xs

-- 帰納原理が生成されていない
#check_failure swapHead.induct

/- `fun_induction` タクティクは、この自動生成された `foo.induct_unfolding` を利用して帰納法を行っています。 -/

/- ## 帰納的述語への応用

帰納原理が自動生成されるのは再帰関数に対してだけで、[帰納的述語](#{root}/Declarative/Inductive.md#InductivePredicate)に対しては生成されません。しかし、帰納的述語を再帰関数として書き直すことができるのであれば、その再帰関数に対して生成された `*.induct` 定理を使って帰納法を行うことができます。

これにより、（再帰関数として書き直せるような）帰納的述語に対しても、帰納法の枝が上手くハマらない問題を解決することができます。
-/

/-- 回文を表す帰納的述語 -/
@[grind]
inductive Palindrome {α : Type} : List α → Prop
  /-- 空リストは回文 -/
  | nil : Palindrome []
  /-- 要素が一つだけのリストは回文 -/
  | single (a : α) : Palindrome [a]
  /-- 回文の両端に同じ要素を追加しても回文 -/
  | sandwich {a : α} {as : List α} (ih : Palindrome as) : Palindrome ([a] ++ as ++ [a])

variable {α : Type}

set_option warn.sorry false in --#

-- 普通に帰納法を使おうとすると、場合分けの枝がうまくはまらない
example (as : List α) (h : as.reverse = as) : Palindrome as := by
  induction as with
  | nil => grind
  | cons a as ih =>
    /-
    ih : as.reverse = as → Palindrome as
    h : (a :: as).reverse = a :: as
    ⊢ Palindrome (a :: as)
    -/
    guard_hyp ih :ₛ as.reverse = as → Palindrome as --#
    guard_hyp h :ₛ (a :: as).reverse = a :: as --#
    guard_target =ₛ Palindrome (a :: as) --#

    -- 簡単には証明できない
    fail_if_success grind
    sorry

-- `α`に対して`(· = ·)`が決定可能という仮定がないため、
-- 古典論理を使用する
open scoped Classical in

/-- 回文判定を行う再帰関数。
`Palindrome` の定義になるべく忠実に書き直したもの -/
def PalindromeRec (as : List α) : Prop :=
  match as with
  | [] => True
  | [a] => True
  | a₁ :: a₂ :: as =>
    let xs := (a₂ :: as).dropLast
    let x := (a₂ :: as).getLast (by simp)

    -- 後に証明に使うときの利便性のために補題を示しておく
    have : [a₁] ++ xs ++ [x] = a₁ :: a₂ :: as := by
      grind [List.dropLast_concat_getLast]

    if a₁ = x then
      PalindromeRec xs
    else
      false
termination_by as.length

-- あっさり証明できる！
example (as : List α) (h : as.reverse = as) : Palindrome as := by
  induction as using PalindromeRec.induct with grind
