/- # テンパズル

解法アイデア
* とりあえず可能な全ての数式を列挙する
* 片っ端から試して、成功したものを全部出力する
-/

/- ## 順列を全て列挙する

まず、与えられた４つの数を並び替えた数列をすべて列挙するというのをやりたい。
ここで `4, 1, 1, 2` のような重複のある数列が与えられた場合、１つめの１と２つめの１は区別したくない。
したがって返り値の型は `HashSet (List α)` とする。
-/
import Batteries

variable {α : Type} [DecidableEq α] [Hashable α]
open Std

/-- リストに与えられた要素を挿入してできるリストを全て返す -/
def List.interleave (x : α) (xs : List α) : List (List α) :=
  match xs with
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (List.interleave x ys).map (y :: ·)

#guard [1, 2].interleave 3 = [[3, 1, 2], [1, 3, 2], [1, 2, 3]]
#guard [1, 1].interleave 2 = [[2, 1, 1], [1, 2, 1], [1, 1, 2]]
#guard [1, 1].interleave 1 = [[1, 1, 1], [1, 1, 1], [1, 1, 1]] -- 重複を許容してしまう

/-- リストのすべての順列（permutation）を生成する関数 -/
def List.permutations (xs : List α) : List (List α) :=
  match xs with
  | [] => [[]]  -- 空リストの順列は、空リスト1つのみ
  | x :: xs =>
    let rest := List.permutations xs  -- 残りの要素の順列を再帰的に生成
    -- 各順列に対して、x をすべての位置に挿入して新たな順列を作る
    rest.map (List.interleave x ·) |>.flatten

#guard [1, 2].permutations = [[1, 2], [2, 1]]
#guard [1, 2, 3, 4].permutations.length = 24
#guard [1, 1].permutations = [[1, 1], [1, 1]] -- 重複を許容してしまう

/-- リストのすべての順列（permutation）を**重複を除いて**生成する関数 -/
def List.permutationSet (xs : List α) : HashSet (List α) :=
  HashSet.ofList (List.permutations xs)

-- 重複を許容しなくなった
#guard (List.permutationSet [1, 1, 1]).toList = [[1, 1, 1]]

/- ## 式を生成する

次のステップとして、与えられた数からなる「四則演算の式」を重複を除いて全部生成する処理を実装する。
-/

/-- 許可されている二項演算 -/
inductive Op where
  /-- 足し算 -/
  | add
  /-- 引き算 -/
  | sub
  /-- 掛け算 -/
  | mul
  /-- 除算。ただし「割り切れるとき」だけ許可するものとする。 -/
  | div
deriving Inhabited

def Op.asList : List Op :=
  [Op.add, Op.sub, Op.mul, Op.div]

protected def Op.toString (op : Op) : String :=
  match op with
  | Op.add => "+"
  | Op.sub => "-"
  | Op.mul => "×"
  | Op.div => "÷"

instance : ToString Op := ⟨Op.toString⟩

/-- 数式 -/
inductive Arith (γ : Type) where
  /-- 数字 -/
  | num (n : γ)
  /-- 二項演算の適用 -/
  | app (op : Op) (l r : Arith γ)
deriving Inhabited

class SafeDiv (γ : Type) where
  safeDiv : γ → γ → Option γ

instance : SafeDiv Int where
  safeDiv x y := if y = 0 || x % y ≠ 0 then none else some (x / y)

instance : SafeDiv Rat where
  safeDiv x y := if y = 0 then none else some (x / y)

variable {γ : Type} [ToString γ] [SafeDiv γ] [Add γ] [Sub γ] [Mul γ]
variable [DecidableEq γ] [Hashable γ]

protected def Arith.toString (expr : Arith γ) : String :=
  match expr with
  | num n => s!"{n}"
  | app op l r =>
    brak l ++ " " ++ ToString.toString op ++ " " ++ brak r
where
  brak : Arith γ → String
  | .num n => toString n
  | e => "(" ++ Arith.toString e ++ ")"

instance : ToString (Arith γ) := ⟨Arith.toString⟩

/-- 与えられた2つの部分式 `l` と `r` に対して、
すべての二項演算子を適用した式のリストを返す関数。

例: `combine 2 3 = [2+3, 2−3, 2×3, 2÷3]` のような式に対応する -/
def Arith.combine (l r : Arith γ) : List (Arith γ) :=
  Op.asList.map (fun op => Arith.app op l r)

/-- あるリストを（要素の順番を保ちながら）２つの空でないリストに分割するすべての方法を返す -/
def List.split (xs : List α) : List (List α × List α) :=
  match xs with
  | [] => []
  | [_x] => []  -- 空でないリストに分割できない
  | x :: xs =>
    let rest := List.split xs |>.map (fun (l, r) => (x :: l, r))
    ([x], xs) :: rest

#guard [1, 2].split = [([1], [2])]
#guard [1, 2, 3].split = [([1], [2, 3]), ([1, 2], [3])]
#guard [1, 2, 3, 4].split = [([1], [2, 3, 4]), ([1, 2], [3, 4]), ([1, 2, 3], [4])]

/-- リストのモナドインスタンス -/
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

/-- リスト `xs` を元に構文木 `Arith` のすべての組み合わせを生成する関数。
ただし、元のリストの要素の順番は保持する。 -/
partial def Arith.ofList (xs : List γ) : List (Arith γ) :=
  match xs with
  | [] => []
  | [n] => [Arith.num n]
  | [x, y] => Arith.combine (Arith.num x) (Arith.num y)
  | xs => do
    let (ls, rs) ← xs.split
    let lArith ← Arith.ofList ls
    let rArith ← Arith.ofList rs
    let arith := Arith.combine lArith rArith
    arith

/-- リスト `xs` を元に構文木 `Arith` のすべての組み合わせを生成する関数。
ただし、元のリストの要素の順番は無視し、すべての順列に対して生成する。 -/
def Arith.ofMultiSet (xs : List γ) : List (Arith γ) := Id.run do
  let permSet := xs.permutationSet
  let mut result := []
  for perm in permSet do
    result := Arith.ofList perm ++ result
  result

#guard
  let actual := (Arith.ofMultiSet [1, 2]).map toString
  let expected := [
    "2 + 1", "2 - 1", "2 × 1", "2 ÷ 1",
    "1 + 2", "1 - 2", "1 × 2", "1 ÷ 2",
  ]
  actual = expected

#guard
  let actual := (Arith.ofMultiSet [1, 1]).map toString
  let expected := ["1 + 1", "1 - 1", "1 × 1", "1 ÷ 1"]
  actual = expected

#guard
  let actual := (Arith.ofMultiSet [1, 1, 1]).map toString
  let expected := [
    "1 + (1 + 1)", "1 - (1 + 1)", "1 × (1 + 1)", "1 ÷ (1 + 1)",
    "1 + (1 - 1)", "1 - (1 - 1)", "1 × (1 - 1)", "1 ÷ (1 - 1)",
    "1 + (1 × 1)", "1 - (1 × 1)", "1 × (1 × 1)", "1 ÷ (1 × 1)",
    "1 + (1 ÷ 1)", "1 - (1 ÷ 1)", "1 × (1 ÷ 1)", "1 ÷ (1 ÷ 1)",
    "(1 + 1) + 1", "(1 + 1) - 1", "(1 + 1) × 1", "(1 + 1) ÷ 1",
    "(1 - 1) + 1", "(1 - 1) - 1", "(1 - 1) × 1", "(1 - 1) ÷ 1",
    "(1 × 1) + 1", "(1 × 1) - 1", "(1 × 1) × 1", "(1 × 1) ÷ 1",
    "(1 ÷ 1) + 1", "(1 ÷ 1) - 1", "(1 ÷ 1) × 1", "(1 ÷ 1) ÷ 1"
  ]
  actual = expected

/- ## 解を列挙する

可能な式を重複を除いてすべて列挙する処理ができたので、その中から解をすべて列挙する処理を実装する。
-/

/-- `Arith` 型で表された数式を評価して、その整数値を `Option Int` として返す関数。
計算不能（ゼロ除算など）の場合は `none` を返す。 -/
def Arith.eval (e : Arith γ) : Option γ :=
  match e with
  | .num n => some n  -- 数字ノードはそのまま返す
  | .app op l r => do
    -- 二項演算子の場合は左右を再帰的に評価
    match op with
    | Op.add =>
      let x ← l.eval
      let y ← r.eval
      return x + y  -- 加算
    | Op.sub =>
      let x ← l.eval
      let y ← r.eval
      return x - y  -- 減算
    | Op.mul =>
      let x ← l.eval
      let y ← r.eval
      return x * y  -- 乗算
    | Op.div =>
      let x ← l.eval
      let y ← r.eval
      SafeDiv.safeDiv x y


def Arith.solutions (nums : List γ) (target : γ) : List (Arith γ) :=
  let expr := Arith.ofMultiSet nums
  expr.filter (fun e => e.eval == some target)

/-- `Rat` 型（有理数）の `Hashable` インスタンス。
    既約形であることが保証されているため、分子・分母の組に基づいてハッシュを構成する。 -/
instance : Hashable Rat where
  -- `r.num` は分子、`r.den` は分母
  hash r := mixHash (hash r.num) (hash r.den)

#eval Arith.solutions [5, 5, 5, 7] (10 : Int)

#eval Arith.solutions [9, 9, 9, 9] (10 : Int)

#eval Arith.solutions [1, 3, 3, 7] (10 : Int)

#eval Arith.solutions [1, 3, 3, 7] (10 : Rat)

#eval Arith.solutions [1, 1, 9, 9] (10 : Rat)

#eval Arith.solutions [1, 1, 5, 8] (10 : Rat)

#eval Arith.solutions [3, 4, 7, 8] (10 : Rat)
