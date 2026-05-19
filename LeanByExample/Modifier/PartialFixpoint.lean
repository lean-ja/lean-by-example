/- # partial_fixpoint

`partial_fixpoint` は、[`partial`](#{root}/Modifier/Partial.md) と同様に「すべての入力に対して必ずしも停止しないような関数」を定義することを可能にしますが、`partial` とは異なり定義した関数を証明に使うことが可能です。
-/
section

  variable {α : Type}

  /-- `partial`で定義された検索関数 -/
  partial def searchP (f : Nat → Option α) (start : Nat) : Option Nat :=
    match f start with
    | some _ => some start
    | none => searchP f (start + 1)

  /-- `partial_fixpoint`で定義された検索関数 -/
  @[grind]
  def searchF (f : Nat → Option α) (start : Nat) : Option Nat :=
    match f start with
    | some _ => some start
    | none => searchF f (start + 1)
  partial_fixpoint

  set_option warn.sorry false --#

  -- `partial`で定義した関数は証明に使うことができない
  example (f : Nat → Option α) (n : Nat) (h : (f n).isSome) : (searchP f n).isSome := by
    induction n with
    | zero =>
      -- 全く展開することができず、上手くいかない
      fail_if_success unfold searchP
      sorry
    | succ n ih =>
      sorry

  -- `partial`で定義したほうは簡約も一切することができない
  /-⋆-//-- info: searchP -/
  #guard_msgs in --#
  #reduce searchP

  -- `searchF`に関しては証明ができる
  example (f : Nat → Option α) (n : Nat) (h : (f n).isSome) : (searchF f n).isSome := by
    induction n with
    | zero =>
      unfold searchF
      grind
    | succ n ih => grind

  /- ## 停止性証明を後回しにしたいとき

  `partial_fixpoint` が特に役立つのは、「停止すること自体は正しそうだが、その証明が定義と複雑に絡み合う」関数です。まず部分関数として定義してから、必要な仕様や全域性をあとで定理として証明できます。
  -/

  /-- `termination_by` だけでは扱いにくいことがある、McCarthy の 91 関数 -/
  def f91 (n : Nat) : Option Nat :=
    if n > 100 then
      pure (n - 10)
    else
      f91 (n + 11) >>= f91
  partial_fixpoint

  theorem f91_spec_high (n : Nat) (h : 100 < n) :
      f91 n = some (n - 10) := by
    unfold f91
    simp [h]

  theorem f91_spec_low (n : Nat) (h₂ : n ≤ 100) :
      f91 n = some 91 := by
    unfold f91
    rw [if_neg (by omega)]
    by_cases h : n < 90
    · rw [f91_spec_low (n + 11) (by omega)]
      simpa using f91_spec_low 91 (by omega)
    · rw [f91_spec_high (n + 11) (by omega)]
      by_cases h' : n = 100
      · simp [f91, h']
      · simpa using f91_spec_low (n + 1) (by omega)
  termination_by 101 - n
  decreasing_by omega

  theorem f91_spec (n : Nat) :
      f91 n = some (if n ≤ 100 then 91 else n - 10) := by
    by_cases h100 : n ≤ 100
    · simp [f91_spec_low, h100]
    · simp [f91_spec_high, Nat.lt_of_not_le h100, h100]

  /- ## 線形探索

  線形探索のように、停止するかどうかが述語 `p` に依存する関数も `partial_fixpoint` で定義できます。`rw [find]` で equation lemma を使っていることに注目してください。`partial` と違って、定義した関数について条件つきの等式推論ができます。
  -/

  def find (i : Nat) (p : Nat → Bool) : Nat :=
    if p i then i else find (i + 1) p
  partial_fixpoint

  theorem find_eq_true_of_exists_ge
      (p : Nat → Bool) (i : Nat) (h : ∃ j ≥ i, p j) :
      p (find i p) = true := by
    obtain ⟨j, h, hpj⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    clear h
    induction k generalizing i with
    | zero =>
      rw [Nat.add_zero] at hpj
      rw [find]
      simp [hpj]
    | succ k ih =>
      rw [find]
      split
      · assumption
      · apply ih
        simpa only [Nat.add_succ, Nat.succ_add] using hpj

  /-
  ただし `find 0 (fun _ => false)` のような入力も Lean の項としては作れてしまいます。`partial_fixpoint` は「常に停止する」と宣言する機能ではなく、「停止しないかもしれない関数についても equation lemma を使った論理的推論をできるようにする」機能だと理解するとよいでしょう。
  -/

end
