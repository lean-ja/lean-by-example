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
