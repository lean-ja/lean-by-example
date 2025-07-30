variable {α : Type}

/--
2つの整列済みリスト `xs` と `ys` をマージして、整列されたリストを返す関数。
`Ord α` 型クラスが必要で、要素の大小を比較できる必要がある。
-/
def merge [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  -- 片方が空なら、もう片方をそのまま返す
  | [], _ => ys
  | _, [] => xs
  -- 両方とも非空の場合
  | x' :: xs', y' :: ys' =>
    match Ord.compare x' y' with
    -- x' の方が小さいか等しい場合は、x' を先頭にして残りを再帰的にマージ
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    -- y' の方が小さい場合は、y' を先頭にして残りを再帰的にマージ
    | .gt => y' :: merge (x' :: xs') ys'

/--
リスト `lst` を2つのリストに分割する関数。
交互に要素を分けることで、ほぼ同じ長さの2リストを作る（マージソートなどに使える）。
-/
def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | [] => ([], []) -- 空リストの場合は、両方とも空リスト
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a) -- 交互に分割

#guard splitList [1, 2, 3] = ([1, 3], [2])
#guard splitList [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4])

/-- `splitList` による分割でリストの長さは増加しない -/
@[grind]
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList lst with grind

/-- `grind`なしで証明したバージョン -/
example (lst : List α) :
  (splitList lst).fst.length ≤ lst.length ∧
  (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList lst with
  | case1 => simp
  | case2 x l a b hl ih =>
    dsimp
    obtain ⟨left, right⟩ := ih
    rw [hl] at left right
    suffices a.length ≤ l.length + 1 from by
      simp_all
    replace left : a.length ≤ l.length := by simp_all
    omega

theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  grind [= splitList.eq_def]

def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : halves.fst.length < xs.length := by
      grind [= splitList.eq_def]
    have : halves.snd.length < xs.length := by
      grind [= splitList.eq_def]
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length -- 入力となるリストの長さが再帰のたびに減少することを指定

#guard mergeSort [5, 3, 22, 15] = [3, 5, 15, 22]



def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok

/- ## Exercises -/

variable (n k : Nat)

example : 0 < n + 1 := by grind

example : 0 ≤ n := by grind

example : (n + 1) - (k + 1) = n - k := by grind

example (h : k < n) : n ≠ 0 := by grind

example : n - n = 0 := by grind

example : n + 1 < k → n < k := by grind
