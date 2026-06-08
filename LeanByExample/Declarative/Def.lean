/-
# def

`def` は、関数や定数など、グローバルに項を定義するための基本的なコマンドです。
-/

/-- 1を足す関数 -/
def addOne (n : Nat) : Nat := n + 1

-- 関数だけでなく定数も定義できる
def foo := "hello"

/- ## 構文ルール

`def` は以下のような構文ルールを持ちます。

* `def` の後に関数名・定数名を書きます。
* 関数名の後に引数を指定します。引数なしだと定数になります。
* 引数の後に `:` によって返り値の型を指定します。返り値の値が関数本体などから推論できる場合は省略できます。
* `:=` の後に関数の本体を書きます。

なお [`theorem`](#{root}/Declarative/Theorem.md) コマンドも同様の構文ルールを持ちます。
-/

/- ## 再帰関数

再帰関数も同様の構文で定義することができます。
-/

/-- 階乗関数 -/
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#guard factorial 7 = 5040

/-
このとき、裏で Lean は再帰関数が停止することの証明を生成しようとし、証明が失敗するとエラーになります。これについて詳しくは以下のページを参照してください。

* [`termination_by`](#{root}/Modifier/TerminationBy.md)
* [`decreasing_by`](#{root}/Modifier/DecreasingBy.md)
* [`partial`](#{root}/Modifier/Partial.md)
* [`partial_fixpoint`](#{root}/Modifier/PartialFixpoint.md)
-/

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

/- ## 名前付き引数

通常は引数をスペース区切りで渡しますが、それだと引数を埋める順番が固定されます。引数の名前を指定して値を渡すこともできて、そうすれば引数の順番を気にする必要はありません。これを **名前付き引数(named arguments)** といいます。
-/

/-- a に 10 を掛けてから b を足す -/
def addAndMul (a b : Int) : Int :=
  10 * a + b

-- 何も指定しないと a, b の順番で引数を渡すことになる
#guard addAndMul 3 2 == 32

-- 引数名を指定して渡すと、引数を好きな順番で渡せる
#guard addAndMul (b := 3) (a := 2) == 23

/- ## 引数のデフォルト値

関数の引数には、デフォルト値を設定することができます。デフォルト値を設定すると、引数を省略して呼び出したときにその値が自動的に使われます。
-/

/-- `name` から挨拶文を生成する -/
def greetWithDefault (name : String) (punct := "!") : String :=
  name ++ "さん、こんにちは" ++ punct

-- `punct` を省略しているが、デフォルトの `!` が使われている
#guard greetWithDefault "山本" == "山本さん、こんにちは!"

/- 明示的に指定したくなった場合は、名前付き引数として渡します。 -/

#guard greetWithDefault "山本" (punct := "!!!") == "山本さん、こんにちは!!!"
