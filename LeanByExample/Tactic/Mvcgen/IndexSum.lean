import Lean

variable {α : Type} [Add α] [Zero α]

/-- 配列に対するインデックスアクセスを使用して和を計算する関数 -/
def Array.sumDo (arr : Array α) : α := Id.run do
  let mut out := 0
  for hi : i in [0:arr.size] do
    out := out + arr[i]
  return out


-- α は加法的な可換モノイド
variable [@Std.Associative α (· + ·)] [@Std.LawfulIdentity α (· + ·) 0]
variable [@Std.Commutative α (· + ·)]

theorem List.sum_append_singleton {l : List α} {x : α} :
    (l ++ [x]).sum = l.sum + x := by
  induction l with (simp_all; grind only)

@[grind =, simp]
theorem Array.sum_append_singleton (arr : Array α) (a : α) :
    (arr ++ #[a]).sum = arr.sum + a := by
  simp [← sum_eq_sum_toList, List.sum_append_singleton]

@[grind =]
theorem Array.extract_stop_add_one {α : Type} {arr : Array α} {i j : Nat}
  (hj : j < arr.size) (hij : i ≤ j) :
    arr.extract i (j + 1) = arr.extract i j ++ #[arr[j]] := by
  simp only [append_singleton, push_extract_getElem, Nat.min_eq_left, hij]


open Std.Do

set_option mvcgen.warning false

/-- `Array.sumDo` は配列の要素の和を正しく計算する -/
theorem Array.sumDo_eq_sum (arr : Array α) : arr.sumDo = arr.sum := by
  generalize h : arr.sumDo = r
  apply Id.of_wp_run_eq h

  mvcgen invariants
  · ⇓⟨cursor, out⟩ => ⌜(arr.take cursor.pos).sum = out⌝
  with (simp_all <;> grind)
