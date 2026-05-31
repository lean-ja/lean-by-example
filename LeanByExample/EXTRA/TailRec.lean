/- # 末尾再帰

**末尾再帰(tail recursion)** とは、再帰呼び出しの結果を加工せずそのまま返り値として返すような再帰のことを指します。そのような再帰関数のことを、**末尾再帰的(tail recursive)** であると言ったりします。

たとえば以下のリストの和を計算する関数は、末尾再帰的ではありません。再帰呼び出しの結果である `sum xs` をそのまま返すのではなく、`(x + ·)` で加工してから返しているからです。
-/
import LeanByExample.Lib.InSecond --#
namespace nonTR --#

variable {α : Type} [Add α] [Zero α]

/-- 末尾再帰的ではない関数の例 -/
def sum (l : List α) : α :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs

#guard sum [1, 2, 3] = 6

end nonTR --#
/-
逆に、以下の関数は末尾再帰的です。再帰呼び出し `sum xs (acc + x)` の結果をそのまま返しているからです。再帰呼び出しの前に、`acc + x` という計算はしていますが、これは引数に入っているだけなので関係ありません。
-/
namespace TR --#

variable {α : Type} [Add α] [Zero α]

/-- 末尾再帰的な関数の例 -/
def sumAux (l : List α) (acc : α) : α :=
  match l with
  | [] => acc
  | x :: xs => sumAux xs (acc + x)

def sum (l : List α) : α :=
  sumAux l 0

#guard sum [1, 2, 3] = 6

end TR --#
/- ## 末尾再帰とコンパイル時最適化

末尾再帰という概念が重要なものとされている主な理由は、末尾再帰的な関数はコンパイル時に最適化してループに変換することができるという事実にあります。

### スタックオーバーフロー

まず前提として、再帰関数の計算はメモリ効率が悪く **スタックオーバーフロー** というエラーを引き起こす可能性が高いということを理解しておく必要があります。たとえば、以下のような関数を考えてみましょう。
-/

/-- 階乗関数 -/
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/- このとき、`factorial 5` の計算の過程を丁寧に書くとこうなります。 -/

example : factorial 5 = 120 := calc
  _ = 5 * factorial 4 := by rfl
  _ = 5 * (4 * factorial 3) := by rfl
  _ = 5 * (4 * (3 * factorial 2)) := by rfl
  _ = 5 * (4 * (3 * (2 * factorial 1))) := by rfl
  _ = 5 * (4 * (3 * (2 * (1 * factorial 0)))) := by rfl
  _ = 5 * (4 * (3 * (2 * (1 * 1)))) := by rfl
  _ = 120 := by rfl

/- ここで重要なのは、最後の `factorial 0` の結果が返ってくるまで、外側の `(5 * ·)` や `(3 * ·)` などの計算がすべて待たされるということです。この待機中の情報はコールスタックという場所に保存されるのですが、容量には限りがあるので大きな入力を計算しようとすると溢れてエラーになります。これがスタックオーバーフローです。
-/

/-
再帰ではなくてループで実装した場合は、入力が大きくなってもコールスタックを食いつぶすことはないので、このことを根拠に「再帰よりループの方がメモリ効率が良い」と言われることがあります。
-/

/-- ループで実装した階乗関数 -/
def factorialLoop (n : Nat) : Nat := Id.run do
  let mut acc := 1
  for i in [1:n+1] do
    acc := acc * i
  return acc

#guard factorialLoop 5 = 120

/- ### 末尾呼び出し最適化

関数が末尾再帰的であった場合、少し様相が異なります。先ほどの階乗関数の例を使って、どのように変わるのかを見てみましょう。まず、階乗関数を末尾再帰を使って書き換えます。
-/

def factorialAux (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => factorialAux n ((n + 1) * acc)

/-- 末尾再帰的な補助関数を使って書き換えた階乗関数 -/
def factorialTR (n : Nat) : Nat :=
  factorialAux n 1

/- そうすると、`factorialTR 5` の計算の過程は以下のようになります。 -/

example : factorialTR 5 = 120 := calc
  _ = factorialAux 5 1 := by rfl
  _ = factorialAux 4 (5 * 1) := by rfl
  _ = factorialAux 3 (4 * (5 * 1)) := by rfl
  _ = factorialAux 2 (3 * (4 * (5 * 1))) := by rfl
  _ = factorialAux 1 (2 * (3 * (4 * (5 * 1)))) := by rfl
  _ = factorialAux 0 (1 * (2 * (3 * (4 * (5 * 1))))) := by rfl
  _ = (1 * (2 * (3 * (4 * (5 * 1))))) := by rfl
  _ = 120 := by rfl

/- よく見ると、引数の計算だけになっていて、再帰呼び出しの結果を待つ必要がなくなっています。したがって、コンパイル時にループに変換することができます。これが **末尾呼び出し最適化(tail call optimization)** です。
-/

/- ### 末尾呼び出し最適化による高速化

Lean のコンパイラは末尾呼び出し最適化を行うため、実際に末尾再帰的な関数に書き換えることによって関数を省メモリかつ高速にすることができます。より顕著な差が出るように、ここではフィボナッチ数列を計算する関数を例にしましょう。（一度の再帰で２つの再帰呼び出しを計算するため、大きな差が出ます）
-/

/-- n 番目のフィボナッチ数を計算する関数 -/
def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

#guard fib 7 = 13


def fibAux (n a b : Nat) : Nat :=
  match n with
  | 0 => a
  | n + 1 => fibAux n b (a + b)

/-- 末尾再帰的に書き直した fib 関数 -/
def fibTR (n : Nat) : Nat := fibAux n 0 1

#guard fibTR 7 = 13

-- 計算に１秒以上かかる
--#--
/-- error: It took more than one second for the command to run. -/
#guard_msgs (error) in
#in_second #eval fib 32
--#--
#eval fib 32

-- 計算がすぐ終わる
#in_second #eval fibTR 32 --#
#eval fibTR 32

/- Lean では「証明では実装 `A` を使用し、実行時は効率的な別の実装 `B` を使用する」ということができるので、実装だけ置き換えて高速化することもできます。詳しくは [`[csimp]`](#{root}/Attribute/Csimp.md) のページを参照してください。 -/

/- ## 末尾再帰と部分関数

末尾再帰性は、[`partial_fixpoint`](#{root}/Modifier/PartialFixpoint.md) で修飾できる関数の条件にも現れます。
詳しくは `partial_fixpoint` のページを参照してください。
-/
