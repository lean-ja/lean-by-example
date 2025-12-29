import Std.Tactic.Do
import Batteries.Data.Array

open Std

variable {α : Type}
variable [LT α] [DecidableLT α]

def ICan'tBelieveItCanSort (arr : Array α) := Id.run do
  let n := arr.size
  let mut vec := arr.toVector
  for hi : i in [0:n] do
    for hj : j in [0:n] do
      if vec[i] < vec[j] then
        vec := vec.swap i j
  return vec.toArray

open Std.Do

set_option mvcgen.warning false

theorem ICan'tBelieveItCanSort_perm (arr : Array α) : Array.Perm (ICan'tBelieveItCanSort arr) arr := by
  generalize h : ICan'tBelieveItCanSort arr = x
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨_cursor, vec⟩ => ⌜Array.Perm arr vec.toArray⌝
  · ⇓⟨_cursor, vec⟩ => ⌜Array.Perm arr vec.toArray⌝
  with grind [Array.Perm.trans, Array.Perm.symm, Array.swap_perm]

@[grind =]
theorem Vector.toArray_extract_size {α : Type} {n : Nat} (v : Vector α n) :
    v.toArray.extract 0 n = v.toArray := by
  grind

@[grind! =>]
theorem List.Cursor.pos_le_length (n : Nat) (xs : [0:n].toList.Cursor) : xs.pos ≤ n := by
  have : xs.prefix.length + xs.suffix.length = n := by
    simp [← List.length_append, xs.property]
  grind only

@[grind <=]
theorem Array.sorted_take_swap {α : Type} [LE α] [IsPreorder α] {arr : Array α}
  (s t : Nat) (hs : s < arr.size) (ht : t < arr.size)
  (h : Array.Pairwise (· ≤ ·) (arr.take s))
  (le1 : arr[s] ≤ arr[t])
  (le2 : ∀ (i : Nat) (_ : i < t), arr[i] ≤ arr[s])
    : Array.Pairwise (· ≤ ·) ((arr.swap s t).take s) := by
  simp [Array.pairwise_iff_getElem] at h ⊢
  grind

@[grind <=]
theorem Array.pairwise_take_succ {α : Type} {R : α → α → Prop} {arr : Array α}
  (k : Nat) (hk : k < arr.size)
  (h : Array.Pairwise R (arr.take k))
  (le : ∀ (i : Nat) (_ : i < arr.size), R arr[i] arr[k])
    : Array.Pairwise R (arr.take (k + 1)) := by
  simp [Array.pairwise_iff_getElem] at h ⊢
  grind

variable [LE α] [IsLinearOrder α] [LawfulOrderLT α]

theorem ICan'tBelieveItCanSort_sorted (arr : Array α) : ICan'tBelieveItCanSort arr |>.Pairwise (· ≤ ·) := by
  generalize h : ICan'tBelieveItCanSort arr = x
  apply Id.of_wp_run_eq h
  mvcgen invariants
  | inv1 => ⇓⟨cursor, vec⟩ =>
    -- 外側のforループの不変条件。
    -- 外側ループが要素`i ∈ [0:n]`を処理する反復の開始時に、
    -- `vec[0...i]`はソート済みである。
    let i := cursor.pos
    ⌜vec.take i |>.toArray.Pairwise (· ≤ ·)⌝
  | inv2 i _ _ _ _ => ⇓⟨cursor, vec⟩ =>
    -- 内側のforループの不変条件。
    -- 外側ループが要素`i ∈ [0:n]`を処理する反復の途中で、
    -- 内側ループが要素`j ∈ [0:n]`を処理する反復の開始時に、以下が成立。
    -- * `vec[0...i]`はソート済み
    -- * `vec[0...j]`のすべての要素は`vec[i]`以下
    let j := cursor.pos
    ⌜(vec.take i |>.toArray.Pairwise (· ≤ ·)) ∧
      ∀ k (_ : k < j), vec[k]'(by grind) ≤ vec[i]'(by grind)⌝
  with (simp at *; grind)
