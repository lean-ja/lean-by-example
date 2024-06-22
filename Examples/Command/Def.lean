/-
# def
`def` は，関数や項を定義するための基本的な構文です．
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

/- なお関数を定義するとき，隣接する同じ型の引数に対しては `:` を使いまわすことができます．-/

def add (n m : Nat) : Nat := n + m

def threeAdd (n m l : Nat) : Nat := n + m + l

/- ## where
`where` キーワードを使うと，定義をする前に変数を使用することができます．主に，ヘルパー関数を宣言するために使用されます．
-/

/-- 整数 `m, n` が与えられたときに `m` 以上 `n` 以下の整数のリストを返す -/
def range (m n : Int) : List Int :=
  loop m (n - m + 1).toNat
where
  loop (start : Int) (length : Nat) : List Int :=
    match length with
    | 0 => []
    | l + 1 => loop start l ++ [start + l]

/- `where` 構文には，複数の式を同時に渡すこともできます．-/

/-- 自然数 `n` の素因数とその重複度のリストを返す -/
partial def primeFactorsMult (n : Nat) : List (Nat × Nat) :=
  loop 2 n [] |>.reverse
where
  /-- 自然数 `d` に対して，`n` の重複度 `μ` を返す.
  つまり `extract d n = (d, μ)` が成り立つ -/
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
