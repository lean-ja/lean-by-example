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
      split <;> simp_all
    | succ n ih => grind

end
