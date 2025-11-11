import Lean

open Std.Do

variable {α : Type}

/-- `takeWhile` を命令型スタイルで実装したもの。
`return` 文を使うバージョン。
（ただし、`result ++ [x]` の部分が非効率的で、あまり高速ではない）
-/
def takeWhileReturn (p : α → Bool) (l : List α) : List α := Id.run do
  let mut result := []
  for x in l do
    if ! p x then
      return result
    result := result ++ [x]
  return result

set_option mvcgen.warning false

@[grind =, simp]
theorem takeWhile_simplify_false (P : α → Bool) (pref suff : List α) (cur : α) (h : P cur = false) :
    List.takeWhile P (pref ++ cur :: suff) = List.takeWhile P pref := by
  fun_induction List.takeWhile with simp_all

@[grind =>]
theorem takeWhile_eq_self_iff_all (P : α → Bool) (l : List α) :
    List.takeWhile P l = l ↔ l.all P := by
  fun_induction List.takeWhile with simp_all

theorem takeWhileReturn_spec (p : α → Bool) (l : List α) :
    takeWhileReturn p l = l.takeWhile p := by
  generalize h : takeWhileReturn p l = r
  apply Id.of_wp_run_eq h

  mvcgen invariants
  · Invariant.withEarlyReturn
    (onContinue := fun cursor result =>
      ⌜result = cursor.prefix ∧ result = cursor.prefix.takeWhile p⌝)
    (onReturn := fun ret result => ⌜ret = result ∧ result = l.takeWhile p⌝)
  with grind

/-- `takeWhile` を命令型スタイルで実装したもの。
`break` 文を使うバージョン。-/
def takeWhileBreak (p : α → Bool) (l : List α) : List α := Id.run do
  let mut result := []
  for x in l do
    if ! p x then
      break
    result := result ++ [x]
  return result

theorem takeWhileBreak_spec (p : α → Bool) (l : List α) :
    takeWhileBreak p l = l.takeWhile p := by
  generalize h : takeWhileBreak p l = r
  apply Id.of_wp_run_eq h

  mvcgen invariants
  · ⇓⟨cursor, result⟩ =>
    -- `return` を使うものと比較すると、不変条件に `cursor.suffix = []` が追加されている。
    -- これは `break` でループを抜けた場合にも成り立つようにするための工夫
    ⌜(cursor.suffix = [] ∨ result = cursor.prefix) ∧ result = cursor.prefix.takeWhile p⌝
  with grind
