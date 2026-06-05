/- # 末尾再帰

**末尾再帰(tail recursion)** とは、再帰呼び出しの結果を加工せずそのまま返り値として返すような再帰のことを指します。そのような再帰関数のことを、**末尾再帰的(tail recursive)** であると言ったりします。

たとえば以下のリストの和を計算する関数は、末尾再帰的ではありません。再帰呼び出しの結果である `sum xs` をそのまま返すのではなく、`(x + ·)` で加工してから返しているからです。
-/
import LeanByExample.Lib.InSecond --#
import LeanByExample.Lib.CheckCsimp --#
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

/-
「末尾再帰の形にすると高速になるのは分かったが、複雑になるから証明に使うときは嫌だなあ」という感想を持たれたでしょうか？実は Lean では「証明では実装 `A` を使用し、実行時は効率的な別の実装 `B` を使用する」ということができます。詳しくは [`[csimp]`](#{root}/Attribute/Csimp.md) のページを参照してください。 -/

/- ## 末尾再帰と部分関数

末尾再帰性は、[`partial_fixpoint`](#{root}/Modifier/PartialFixpoint.md) で修飾できる関数の条件にも現れます。
詳しくは `partial_fixpoint` のページを参照してください。
-/

/- ## 関数を末尾再帰化するテクニック

再帰関数を末尾再帰的な形に書き換えるために、さまざまなテクニックが知られています。

### 蓄積変数を導入する

再帰呼び出しの結果を加工する代わりに、引数を増やしてその中で計算を行うというテクニックです。このとき増やす引数のことを **蓄積変数(accumulator)** と呼びます。
-/
namespace Accum --#

/-- リストを逆順にする関数の、末尾再帰的でない実装 -/
@[grind =]
def reverse (l : List α) : List α :=
  match l with
  | [] => []
  | x :: xs => reverse xs ++ [x]

@[grind =]
def reverseAux (l : List α) (acc : List α) : List α :=
  match l with
  | [] => acc
  | x :: xs => reverseAux xs (x :: acc)

/-- リストを逆順にする関数の、末尾再帰的な実装 -/
@[grind =]
def reverseTR (l : List α) : List α := reverseAux l []

@[simp, grind =]
theorem reverseAux_lem (l : List α) (acc : List α)
    : reverseAux l acc = reverse l ++ acc := by
  induction l generalizing acc with grind

/-- `reverse` と `reverseTR` は等しい -/
theorem reverse_eq_reverseTR (l : List α) : reverse l = reverseTR l := by
  induction l with grind

end Accum --#
/- ### foldl / foldr を使う

再帰パターンを抽出した高階関数として `List.foldl` と `List.foldr` がありますが、この２つは「`List.foldl` の方は末尾再帰的で、`List.foldr` の方はそうではない」という違いがあります。

しかし、Lean の標準ライブラリにおいて `List.foldr` は末尾再帰的な実装と `[csimp]` 属性を利用して置換されています。
-/
--#--
/-- info: List.foldr_eq_foldrTR has the [csimp] attribute -/
#guard_msgs in
#check_csimp List.foldr_eq_foldrTR
--#--
/- したがって `foldr` 的な再帰構造を持つ関数を `List.foldr` を使って書き直すだけで、実行時に末尾呼び出し最適化の恩恵を受けることができます。
-/
namespace Fold --#

variable [Add α] [Zero α]

/-- 合計を求める関数 -/
def sum (l : List α) : α :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs

/-- 合計を求める関数を `foldr` で書き直したもの -/
def sumFoldr (l : List α) : α :=
  List.foldr (· + ·) 0 l

theorem sum_eq_sumFoldr (l : List α) : sum l = sumFoldr l := by
  delta sumFoldr sum List.foldr
  rfl

end Fold --#
/- ### 継続渡しスタイルにする

「値を受け取った後に残りの計算をどう続けるか」を表す関数のことを **継続(continuation)** と呼びます。
「再帰呼び出しの結果を受け取った後に何をするか」を継続として明示的に渡すという方法です。**継続渡しスタイル(continuation-passing style)** と呼ばれます。
-/
namespace CPS --#

def map (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | x :: xs => f x :: map f xs

/-- 継続渡しスタイルに書き直すための補助関数 -/
def mapCPSAux (f : α → β) (l : List α) (k : List β → List β) : List β :=
  match l with
  | [] => k []
  | x :: xs =>
    mapCPSAux f xs (fun ys => k (f x :: ys))

/-- 継続渡しスタイルに書き直した map 関数 -/
def mapCPS (f : α → β) (l : List α) : List β :=
  mapCPSAux f l id

theorem mapCPSAux_lem (f : α → β) (l : List α) (k : List β → List β)
    : mapCPSAux f l k = k (map f l) := by
  induction l generalizing k with
  | nil => rfl
  | cons x xs ih => solve_by_elim

/-- `map` と `mapCPS` は等しい -/
theorem map_eq_mapCPS (f : α → β) (l : List α) : map f l = mapCPS f l := by
  delta mapCPS
  simp [mapCPSAux_lem]

end CPS --#
