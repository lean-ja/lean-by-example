import Lean

#check List.replicate_append_replicate
#check List.replicate_succ
#check Array.toList_inj
#check Array.toList_append
#check Array.toList_replicate
#check Array.filter_beq
#check Vector.toArray_set
#print Array.toVector
#check Vector.getElem_toArray
#check Array.size_toList
#check Array.length_toList
#check Array.toList_length
#check Array.size_eq_length_toList

/-!
#check List.countP_eq_length_filter
#check List.countP_filter
#check List.countP_append
#check List.filter_append
#check List.filter_cons_of_pos
#check List.filter_cons_of_neg
#check List.filter_eq_self
#check List.eq_replicate_iff
#check Array.toList_filter
#check Array.filter_beq
#check Array.countP_eq_size_filter
#check Array.size_eq_countP_add_countP
#check Array.count_eq_countP
#check eq_of_beq
#check beq_iff_eq
#check Bool.not_eq_true
#check List.take_succ
#check List.take_concat_get
#check List.take_append_get
#check List.getElem?_eq_getElem
#check List.getElem_take
#check List.getElem_of_eq
#check Array.toList_extract
#check Array.toArray_toList
#check List.concat_eq_append
#check Vector.getElem_set!
#check Vector.getElem_set
#check Array.getElem_setIfInBounds
#check Vector.toArray_set!
#check Array.set!_eq_setIfInBounds
#print Vector.set!
#print Array.toVector
#check Vector.getElem_toArray
-/

theorem test_count {α : Type} [BEq α] [LawfulBEq α] (xs : Array α) (x : α) :
    xs.size - (xs.filter (fun y => y != x)).size = xs.count x := by
  have hsize := Array.size_eq_countP_add_countP (p := fun y => y != x) (xs := xs)
  rw [Array.countP_eq_size_filter] at hsize
  have hcount :
      Array.countP (fun y => decide ¬(y != x) = true) xs = xs.count x := by
    rw [Array.count_eq_countP]
    apply Array.countP_congr
    intro y hy
    by_cases h : y == x
    · have hyx : y = x := eq_of_beq h
      subst hyx
      simp
    · have hyx : y ≠ x := by
        intro hyx
        subst hyx
        simp at h
      simp [h, hyx]
  omega
