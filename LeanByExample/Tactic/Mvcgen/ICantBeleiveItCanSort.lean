import Std.Tactic.Do
import Batteries

open Std

variable {α : Type}
variable [LT α] [DecidableLT α]

@[grind =]
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

@[simp, grind =]
theorem Vector.toArray_extract_size {α : Type} {n : Nat} (v : Vector α n) :
    v.toArray.extract 0 n = v.toArray := by
  grind

variable [LE α] [IsLinearOrder α] [LawfulOrderLT α]

@[grind! =>]
theorem cursor_pos_le_length (n : Nat) (xs : [0:n].toList.Cursor) : xs.pos ≤ n := by
  have : xs.prefix.length + xs.suffix.length = n := by
    simp [← List.length_append, xs.property]
  grind only

@[simp]
theorem lem1 {n cur : Nat} (pref suff : List Nat) (h : [:n].toList = pref ++ cur :: suff) :
    pref.length = cur := by
  grind

theorem lem3 {α : Type} [LE α] [IsPartialOrder α] {b : Array α}
  (k j : Nat) (hk : k < b.size) (hj : j < b.size)
  (h : Array.Pairwise (· ≤ ·) (b.take k))
  (h2 : b[k] ≤ b[j])
  (h3 : ∀ (i : Nat) (x : i < j), b[i] ≤ b[k])
    : Array.Pairwise (· ≤ ·) ((b.swap k j).take k) := by
  simp [Array.pairwise_iff_getElem] at *
  grind

grind_pattern lem3 => Array.Pairwise (· ≤ ·) ((b.swap k j).take k)


theorem ICan'tBelieveItCanSort_sorted (arr : Array α) : ICan'tBelieveItCanSort arr |>.Pairwise (· ≤ ·) := by
  generalize h : ICan'tBelieveItCanSort arr = x
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨cursor, vec⟩ => ⌜vec.take cursor.pos |>.toArray.Pairwise (· ≤ ·)⌝
  · ⇓⟨cursor, vec⟩ => by
    expose_names
    exact ⌜(vec.take cur |>.toArray.Pairwise (· ≤ ·)) ∧
      ∀ i (_ : i < cursor.pos), vec[i]'(by grind) ≤ vec[cur]'(by grind)⌝
  with grind

  case vc4 =>
    expose_names
    simp (disch := assumption) at *
    simp [Array.pairwise_iff_getElem] at *
    grind
