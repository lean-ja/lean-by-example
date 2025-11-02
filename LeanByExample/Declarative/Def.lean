/-
# def
`def` は、関数や定数などの項を定義するための基本的なコマンドです。
-/

def foo := "hello"

/-- 1を足す関数 -/
def addOne (n : Nat) : Nat := n + 1

/- 再帰関数も定義することができます。（このとき、裏で Lean は再帰関数が停止することの証明を生成しようとします。証明が失敗するとエラーになります。これについて詳しくは [`termination_by`](#{root}/Modifier/TerminationBy.md) や [`decreasing_by`](#{root}/Modifier/DecreasingBy.md) のページを参照してください。）-/

/-- 階乗関数 -/
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#guard factorial 7 = 5040

/- ## 引数の指定

関数を定義するとき、隣接する同じ型の引数に対しては `:` を使いまわすことができます。-/

def add (n m : Nat) : Nat := n + m

def threeAdd (n m l : Nat) : Nat := n + m + l

/- また丸括弧 `()` ではなくて波括弧で引数を指定すると、その引数は[暗黙の引数](#{root}/Syntax/ImplicitBinder.md)になり、Lean が推論して埋めてくれるようになります。 -/

/-- リストの長さを返す -/
def List.myLength {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: xs => 1 + myLength xs

-- `α` を引数として与えなくても呼び出すことができる
#guard List.myLength [1, 2, 3] = 3
