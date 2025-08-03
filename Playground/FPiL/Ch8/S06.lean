import Lean

section
variable {α : Type}

/--
配列 `arr` の `i` 番目の要素を、挿入ソートの要領で整列させる。

前提：`arr[0 : i]` はすでに昇順にソートされているとする。
この関数は `arr[i]` を適切な位置に挿入することで `arr[0 : i+1]` を昇順にソートされた状態にする。
-/
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by omega
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      have : (dbgTraceIfShared "array to swap" arr).size = arr.size := by
        simp [dbgTraceIfShared]
      insertSorted (((dbgTraceIfShared "array to swap" arr)).swap i' i) ⟨i', by simp [*]⟩

#eval insertSorted #[5, 3, 8, 1, 2] ⟨3, by grind⟩

@[grind]
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  fun_induction insertSorted <;> simp_all

/-- 配列 `arr` に `insertSorted` を繰り返し適用して整列させていく。
`insertSorted arr i` を `i, i + 1, ..., arr.size - 1` に対して適用する。
-/
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by grind
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i

/-- 配列を挿入ソートで整列する -/
def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0

#eval insertionSortLoop #[5, 3, 8, 1, 2, 9, 2, 2, 35, 2] 3

end

/- ## Exercise

Write a function that reverses arrays. Test that if the input array has a reference count of one, then your function does not allocate a new array.
-/

#check Array.swap
#check Array.set!

/-- **TODO** なぜ標準ライブラリに Array.swap! 関数がないのか？
→ ある。

<https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/Init/Data/Array/Basic.lean#L268>
-/
def Array.swap! {α : Type} [Inhabited α] (xs : Array α) (i j : Nat) : Array α := Id.run do
  let mut xs := xs
  let ai := xs[i]!
  let aj := xs[j]!
  xs := xs.set! i aj
  xs := xs.set! j ai
  return xs

variable {α : Type} [Inhabited α]

/-- インデックスアクセスの妥当性を証明しないバージョン -/
def Array.myReverse! (arr : Array α) : Array α := Id.run do
  let mut array := arr
  let size := array.size
  for i in [0 : size / 2] do
    array := array.swapIfInBounds i (size - 1 - i)
  return array

#guard Array.myReverse! #[1, 2, 3, 4, 5] = #[5, 4, 3, 2, 1]
#guard Array.myReverse! (α := Nat) #[] = #[]

def Array.myReverse (arr : Array α) : Array α := Id.run do
  let mut array := arr
  let size := array.size -- 可変な配列なので、`size = array.size` が常に成り立つとは限らない
  for h : i in [0 : size / 2] do
    have : i < array.size := by
      dsimp [(· ∈ ·)] at h
      fail_if_success grind
      sorry
    have : size - 1 - i < array.size := by
      dsimp [(· ∈ ·)] at h
      fail_if_success grind
      sorry
    array := array.swap i (size - 1 - i)
  return array

def Array.myReverseVec (arr : Array α) : Array α := Id.run do
  let mut vec := arr.toVector
  let size := vec.size
  for h : i in [0 : size / 2] do
    have : i < vec.size := by
      dsimp [(· ∈ ·)] at h
      grind
    have : size - 1 - i < vec.size := by
      dsimp [(· ∈ ·)] at h
      grind
    vec := vec.swap i (size - 1 - i)
  return vec.toArray
