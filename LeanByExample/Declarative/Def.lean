/-
# def
`def` は、関数や項を定義するための基本的なコマンドです。
-/

def foo := "hello"

/-- 1を足す -/
def addOne (n : Nat) : Nat := n + 1

/-- 階乗関数 -/
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#guard factorial 7 = 5040

/- なお関数を定義するとき、隣接する同じ型の引数に対しては `:` を使いまわすことができます。-/

def add (n m : Nat) : Nat := n + m

def threeAdd (n m l : Nat) : Nat := n + m + l

/- ## where 句 { #Where }
`where` 句を使うと、定義をする前に変数を使用することができます。主に、ヘルパー関数を宣言するために使用されます。
-/

/-- 自然数 `n` の素因数とその重複度のリストを返す -/
partial def primeFactorsMult (n : Nat) : List (Nat × Nat) :=
  loop 2 n [] |>.reverse
where
  /-- 自然数 `d` に対して、`n` の重複度 `μ` と `d` のペア `(d, μ)` を返す。-/
  extract (d n : Nat) : Nat × Nat :=
    if d ≤ 1 then
      (1, 0)
    else if n % d != 0 then
      (d, 0)
    else
      let (d, m) := extract d (n / d)
      (d, m + 1)

  /-- ヘルパー関数 -/
  loop (d target : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    if target ≤ 1 then
      acc
    else
      let (d, m) := extract d target
      if m = 0 then
        loop (d + 1) target acc
      else
        loop (d + 1) (target / (d ^ m)) ((d, m) :: acc)

/- ## termination_by 句 { #TerminationBy }
`termination_by` 句は、再帰関数が有限回の再帰で停止することを Lean にわかってもらうために、「再帰のたびに減少する指標」を指定します。
-/
-- 何も指定しないと、停止することが Lean にはわからないのでエラーになる
/--
error: fail to show termination for
  M
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    M (n + 11)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬n > 100
⊢ n + 11 < n
-/
#guard_msgs in
  /-- McCarthy の 91 関数 -/
  def M (n : Nat) : Nat :=
    if n > 100 then
      n - 10
    else
      M (M (n + 11))

/- 以下のように、`termination_by` で「再帰適用で減少していくもの」を指定することができ、うまくいけばエラーがなくなります。-/

/-- McCarthy の 91 関数 -/
def Mc91 (n : Nat) : Nat :=
  (M n).val
where
  M (n : Nat) : { m : Nat // m ≥ n - 10 } :=
    if h : n > 100 then
      ⟨n - 10, by omega⟩
    else
      have : n + 11 - 10 ≤ M (n + 11) := (M (n + 11)).property
      have lem : n - 10 ≤ M (M (n + 11)) := calc
        n - 10 ≤ (n + 11) - 10 - 10 := by omega
        _ ≤ (M (n + 11)) - 10 := by omega
        _ ≤ M (M (n + 11)) := (M (M (n + 11)).val).property

      ⟨M (M (n + 11)), lem⟩
  termination_by 101 - n
