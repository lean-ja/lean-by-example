import Lean

open Std.Do

set_option mvcgen.warning false

variable [BEq α] [Inhabited α]

def Array.moveLast (xs : Array α) (x : α) : Array α :=
  xs.filter (· != x) ++ xs.filter (· == x)

def Array.moveLastInPlace (xs : Array α) (x : α) : Array α := Id.run do
  let n := xs.size
  let mut ys : Vector α n := xs.toVector
  let mut write := 0

  for hi : i in [0:n] do
    if ys[i] != x then
      ys := ys.set! write ys[i]
      write := write + 1

  let write0 := write
  for hi : i in [write0:n] do
    ys := ys.set i x

  return ys.toArray

theorem Array.filter_extract_succ_right_of_pos {α : Type} {xs : Array α}
    {p : α -> Bool} {i : Nat} (hi : i < xs.size) (hp : p xs[i]) :
    (xs.extract 0 (i + 1)).filter p = ((xs.extract 0 i).filter p).push xs[i] := by
  rw [Array.extract_succ_right (w := by omega) hi]
  rw [Array.filter_push_of_pos (h := hp) (w := by simp [Array.size_extract]; omega)]

theorem Array.filter_extract_succ_right_of_neg {α : Type} {xs : Array α}
    {p : α -> Bool} {i : Nat} (hi : i < xs.size) (hp : ¬ p xs[i]) :
    (xs.extract 0 (i + 1)).filter p = (xs.extract 0 i).filter p := by
  rw [Array.extract_succ_right (w := by omega) hi]
  rw [Array.filter_push_of_neg (h := hp) (w := by simp [Array.size_extract]; omega)]

theorem Array.extract_set_next {α : Type} {xs : Array α}
    {i : Nat} {a : α} (hi : i < xs.size) :
    (xs.set i a hi).extract 0 (i + 1) = (xs.extract 0 i).push a := by
  rw [← Array.toList_inj]
  simp [List.extract_eq_take_drop, List.set_eq_take_append_cons_drop, hi]
  have hlen : (xs.toList.take i).length = i := by
    simp [Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [show i + 1 = (xs.toList.take i).length + 1 by omega]
  rw [List.take_length_add_append]
  simp

theorem Array.extract_setIfInBounds_next {α : Type} {xs : Array α}
    {i : Nat} {a : α} (hi : i < xs.size) :
    (xs.setIfInBounds i a).extract 0 (i + 1) = (xs.extract 0 i).push a := by
  rw [Array.setIfInBounds_def]
  simp [hi, Array.extract_set_next]

theorem Vector.extract_set_next {α : Type} {n : Nat} {xs : Vector α n}
    {i : Nat} {a : α} (hi : i < n) :
    (xs.set i a).toArray.extract 0 (i + 1) = (xs.toArray.extract 0 i).push a := by
  simpa using Array.extract_set_next (xs := xs.toArray) (i := i) (a := a) (by simpa)

theorem Vector.extract_set!_next {α : Type} {n : Nat} {xs : Vector α n}
    {i : Nat} {a : α} (hi : i < n) :
    (xs.set! i a).toArray.extract 0 (i + 1) = (xs.toArray.extract 0 i).push a := by
  simpa using Array.extract_setIfInBounds_next (xs := xs.toArray) (i := i) (a := a) (by simpa)

theorem Array.toList_extract_zero {α : Type} (xs : Array α) (i : Nat) :
    (xs.extract 0 i).toList = xs.toList.take i := by
  simp [Array.toList_extract, List.extract_eq_take_drop]

theorem List.take_length_eq_self {α : Type} (xs : List α) :
    xs.take xs.length = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem Array.extract_all_toList {α : Type} (xs : Array α) :
    (xs.extract 0 xs.size).toList = xs.toList := by
  simp

theorem Vector.extract_set_next_toList {α : Type} {n : Nat} {xs : Vector α n}
    {i : Nat} {a : α} (hi : i < n) :
    ((xs.set i a).toArray.extract 0 (i + 1)).toList =
      (xs.toArray.extract 0 i).toList ++ [a] := by
  rw [Vector.extract_set_next hi]
  simp

theorem Vector.extract_set!_next_toList {α : Type} {n : Nat} {xs : Vector α n}
    {i : Nat} {a : α} (hi : i < n) :
    ((xs.set! i a).toArray.extract 0 (i + 1)).toList =
      (xs.toArray.extract 0 i).toList ++ [a] := by
  rw [Vector.extract_set!_next hi]
  simp

theorem Vector.getElem_set!_of_ne {α : Type} {n : Nat} {xs : Vector α n}
    {i j : Nat} {a : α} (hj : j < n) (hij : i ≠ j) :
    (xs.set! i a)[j] = xs[j] := by
  simp [Vector.set!, Array.set!_eq_setIfInBounds, hj, hij]

theorem List.replicate_succ_append {α : Type} (n : Nat) (x : α) :
    List.replicate (n + 1) x = List.replicate n x ++ [x] := by
  simpa using
    (List.replicate_append_replicate (n := n) (m := 1) (a := x)).symm

theorem List.filter_take_succ_of_pos {α : Type} {xs : List α}
    {p : α -> Bool} {i : Nat} (hi : i < xs.length) (hp : p xs[i]) :
    (xs.take (i + 1)).filter p = (xs.take i).filter p ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => cases hi
  | cons a xs ih =>
      cases i with
      | zero =>
          simp at hp ⊢
          exact hp
      | succ i =>
          have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
          have hp' : p xs[i] := hp
          have hih := ih hi' hp'
          by_cases ha : p a
          · simp [List.take, ha, hih]
          · have ha' : p a = false := by
              cases h : p a <;> simp_all
            simp [List.take, ha', hih]

theorem List.filter_take_succ_of_neg {α : Type} {xs : List α}
    {p : α -> Bool} {i : Nat} (hi : i < xs.length) (hp : ¬ p xs[i]) :
    (xs.take (i + 1)).filter p = (xs.take i).filter p := by
  induction xs generalizing i with
  | nil => cases hi
  | cons a xs ih =>
      cases i with
      | zero =>
          have hp' : p a = false := by
            cases h : p a <;> simp_all
          simp [hp']
      | succ i =>
          have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
          have hp' : ¬ p xs[i] := hp
          have hih := ih hi' hp'
          by_cases ha : p a
          · simp [List.take, ha, hih]
          · have ha' : p a = false := by
              cases h : p a <;> simp_all
            simp [List.take, ha', hih]

theorem Array.size_sub_filter_ne_eq_count {α : Type} [BEq α] [LawfulBEq α]
    (xs : Array α) (x : α) :
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

theorem Vector.extract_set!_filter_extract_succ_of_pos {α : Type} {n : Nat}
    {ys : Vector α n} {xs : Array α} {p : α -> Bool} {i write : Nat}
    (hwrite : write < n) (hi : i < xs.size) (hin : i < n)
    (hprefix : ys.toArray.extract 0 write = (xs.extract 0 i).filter p)
    (hread : ys[i] = xs[i]) (hp : p ys[i]) :
    (ys.set! write ys[i]).toArray.extract 0 (write + 1) =
      (xs.extract 0 (i + 1)).filter p := by
  rw [Vector.extract_set!_next hwrite]
  rw [hprefix]
  have hpx : p xs[i] := by simpa [hread] using hp
  rw [Array.filter_extract_succ_right_of_pos hi hpx]
  simp [hread]

attribute [grind =] Array.filter_extract_succ_right_of_pos
attribute [grind =] Array.filter_extract_succ_right_of_neg
attribute [grind =] Array.extract_setIfInBounds_next
attribute [grind =] Vector.extract_set_next
attribute [grind =] Vector.extract_set!_next
attribute [grind =] Array.toList_extract_zero
attribute [grind =] Vector.extract_set_next_toList
attribute [grind =] Vector.extract_set!_next_toList
attribute [grind =] Vector.getElem_set!_of_ne

grind_pattern Vector.extract_set!_filter_extract_succ_of_pos =>
  (ys.set! write ys[i]).toArray.extract 0 (write + 1),
  (xs.extract 0 (i + 1)).filter p

theorem scratch_moveLastInPlace_eq_moveLast
    {α : Type} [BEq α] [LawfulBEq α] [Inhabited α] (xs : Array α) (x : α) :
    Array.moveLastInPlace xs x = Array.moveLast xs x := by
  generalize h : Array.moveLastInPlace xs x = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨cursor, write, ys⟩ => by
      expose_names
      exact ⌜
        (ys.toArray.extract 0 write).toList =
          (xs.toList.take cursor.prefix.length).filter (· != x) ∧
        write = ((xs.toList.take cursor.prefix.length).filter (· != x)).length ∧
        write ≤ cursor.prefix.length ∧
        (∀ (j : Nat) (hj : j < n), cursor.prefix.length ≤ j -> ys[j] = xs[j])⌝
  · ⇓⟨cursor, ys⟩ => by
      expose_names
      exact ⌜
        (ys.toArray.extract 0 (write0 + cursor.prefix.length)).toList =
          (xs.filter (· != x)).toList ++
          List.replicate cursor.prefix.length x ∧
        write0 = (xs.filter (· != x)).toList.length ∧
        write0 + cursor.prefix.length ≤ n⌝
  case vc1.step.isTrue =>
    rename_i pref cur suff hrange b write ys hcond hinv
    rcases hinv with ⟨hprefix, hwrite, hwrite_le, htail⟩
    have hcur : cur = pref.length := by grind
    subst cur
    have hcur_lt : pref.length < xs.size := by grind
    have hread : ys[pref.length] = xs[pref.length] := by
      simpa [ys] using htail pref.length (by simpa using hcur_lt) (by omega)
    have hread' : b.snd[pref.length] = xs[pref.length] := by
      simpa [ys] using hread
    have hwrite_lt : b.fst < xs.size := by omega
    have hp : (fun y => y != x) xs[pref.length] := by
      simpa [hread] using hcond
    have hf :
        (xs.toList.take (pref.length + 1)).filter (fun y => y != x) =
          (xs.toList.take pref.length).filter (fun y => y != x) ++ [xs[pref.length]] :=
      List.filter_take_succ_of_pos (xs := xs.toList) (p := fun y => y != x)
        (i := pref.length) (by simpa using hcur_lt) hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [write, ys]
      rw [Vector.extract_set!_next_toList (by simpa using hwrite_lt), hprefix]
      rw [show (pref ++ [pref.length]).length = pref.length + 1 by simp]
      rw [hf]
      simp [hread']
    · dsimp only [write]
      rw [hwrite]
      rw [show (pref ++ [pref.length]).length = pref.length + 1 by simp]
      rw [hf]
      simp
    · change b.fst + 1 ≤ (pref ++ [pref.length]).length
      rw [show (pref ++ [pref.length]).length = pref.length + 1 by simp]
      omega
    · intro j hj hjge
      have hge : pref.length + 1 ≤ j := by
        simpa [show (pref ++ [pref.length]).length = pref.length + 1 by simp] using hjge
      have hne : b.fst ≠ j := by omega
      dsimp only [write, ys]
      rw [Vector.getElem_set!_of_ne hj hne]
      exact htail j hj (by omega)
  case vc2.step.isFalse =>
    rename_i pref cur suff hrange b write ys hcond hinv
    rcases hinv with ⟨hprefix, hwrite, hwrite_le, htail⟩
    have hcur : cur = pref.length := by grind
    subst cur
    have hcur_lt : pref.length < xs.size := by grind
    have hread : ys[pref.length] = xs[pref.length] := by
      simpa [ys] using htail pref.length (by simpa using hcur_lt) (by omega)
    have hp : ¬ (fun y => y != x) xs[pref.length] := by
      intro hp
      exact hcond (by simpa [hread] using hp)
    have hf :
        (xs.toList.take (pref.length + 1)).filter (fun y => y != x) =
          (xs.toList.take pref.length).filter (fun y => y != x) :=
      List.filter_take_succ_of_neg (xs := xs.toList) (p := fun y => y != x)
        (i := pref.length) (by simpa using hcur_lt) hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [write, ys]
      rw [hprefix]
      rw [show (pref ++ [pref.length]).length = pref.length + 1 by simp]
      rw [hf]
    · dsimp only [write]
      rw [hwrite]
      rw [show (pref ++ [pref.length]).length = pref.length + 1 by simp]
      rw [hf]
    · change b.fst ≤ (pref ++ [pref.length]).length
      rw [show (pref ++ [pref.length]).length = pref.length + 1 by simp]
      omega
    · intro j hj hjge
      exact htail j hj (by
        have hge : pref.length + 1 ≤ j := by
          simpa [show (pref ++ [pref.length]).length = pref.length + 1 by simp] using hjge
        omega)
  case vc3.pre =>
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro j hj _
    rfl
  case vc4.step =>
    rename_i r_1 write0 hfirst pref cur suff hrange b hinv
    rcases hinv with ⟨hprefix, hwrite0, hle⟩
    have hcur : cur = write0 + pref.length := by grind
    subst cur
    have hcur_lt : write0 + pref.length < xs.size := by grind
    refine ⟨?_, hwrite0, ?_⟩
    · rw [show write0 + (pref ++ [write0 + pref.length]).length =
          write0 + pref.length + 1 by simp [Nat.add_assoc]]
      rw [Vector.extract_set_next_toList (xs := b) (i := write0 + pref.length)
        (a := x) (by simpa using hcur_lt)]
      rw [hprefix]
      rw [show (pref ++ [write0 + pref.length]).length = pref.length + 1 by simp]
      rw [List.replicate_succ_append]
      simp [List.append_assoc]
    · rw [show (pref ++ [write0 + pref.length]).length = pref.length + 1 by simp]
      omega
  case vc5.post.success.pre =>
    rename_i n ys r_1 write0 hfirst
    rcases hfirst with ⟨hprefix, hwrite, hle, htail⟩
    have htake : xs.toList.take [:n].toList.length = xs.toList := by
      rw [show [:n].toList.length = xs.toList.length by simp [n]]
      exact List.take_length_eq_self xs.toList
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [write0]
      simp only [List.length_nil, Nat.add_zero, List.replicate, List.append_nil]
      rw [hprefix]
      rw [htake]
      simp
    · dsimp only [write0]
      rw [hwrite]
      rw [htake]
      simp
    · dsimp only [write0]
      simpa [n] using hle
  case vc6.post.success.post.success =>
    rename_i n ys r_1 write0 hfirst r hsecond
    rcases hsecond with ⟨hprefix, hwrite0, hle⟩
    rw [← Array.toList_inj]
    have hwrite0_size : write0 = (xs.filter (fun y => y != x)).size := by
      rw [hwrite0]
      simpa using (Array.length_toList (xs := xs.filter (fun y => y != x)))
    have hend : write0 + [write0:n].toList.length = n := by
      simp
      omega
    have hrlist :
        r.toArray.toList =
          (xs.filter (fun y => y != x)).toList ++
          List.replicate [write0:n].toList.length x := by
      have hfull :
          (r.toArray.extract 0 (write0 + [write0:n].toList.length)).toList =
            r.toArray.toList := by
        rw [hend]
        simpa using Array.extract_all_toList r.toArray
      rw [← hfull]
      exact hprefix
    rw [hrlist]
    unfold Array.moveLast
    rw [Array.filter_beq (xs := xs) x]
    simp [Array.toList_append, Array.toList_replicate]
    congr 1
    rw [show n = xs.size by simp [n]]
    rw [hwrite0_size]
    exact Array.size_sub_filter_ne_eq_count xs x
