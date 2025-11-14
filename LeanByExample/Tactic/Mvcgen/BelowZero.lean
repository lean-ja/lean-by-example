import Std.Tactic.Do

/-- `operations : List Int` を先頭から順に足していったときに、
どこかの時点で合計値が 0 未満になることがあるか判定する -/
def belowZero (operations : List Int) : Bool := Id.run do
  let mut balance := 0
  for op in operations do
    balance := balance + op
    if balance < 0 then
      return true
  return false

namespace List

variable {α : Type}

/-- リスト `l` の先頭からある部分までを取り出せば述語 `P : List α → Prop` が成り立つ -/
def HasPrefix (P : List α → Prop) (l : List α) : Prop := ∃ n, P (l.take n)

/-- `HasPrefix` の定義を言い換えるだけの定義 -/
theorem hasPrefix_iff {P : List α → Prop} {l : List α} :
    l.HasPrefix P ↔ ∃ n, P (l.take n) := by
  simp [HasPrefix]

/-- 空リストの接頭辞は自分しかない -/
@[simp, grind =]
theorem hasPrefix_nil {P : List α → Prop} : [].HasPrefix P ↔ P [] := by
  simp [hasPrefix_iff]

/-- 空リストに対して成り立つなら、接頭辞に対しても成り立つ -/
@[simp, grind =>]
theorem hasPrefix_of_nil {P : List α → Prop} {l : List α} (h : P []) : l.HasPrefix P := by
  exists 0

/-- 全体に対して成り立つなら、接頭辞に対しても成り立つ -/
@[simp, grind =>]
theorem hasPrefix_of_all {P : List α → Prop} {l : List α} (h : P l) : l.HasPrefix P := by
  exists l.length
  simpa

@[grind =]
theorem hasPrefix_cons {P : List α → Prop} {a : α} {l : List α} :
    (a :: l).HasPrefix P ↔ P [] ∨ l.HasPrefix (fun l' => P (a :: l')) := by
  constructor
  · intro ⟨n, hn⟩
    by_cases nzero : n = 0
    · simp_all
    · right
      exists n - 1
      suffices a :: take (n - 1) l = take n (a :: l) from by
        simp_all
      grind [take_cons]
  · rintro (h | ⟨⟨n, hn⟩⟩)
    · grind
    · exists n + 1

@[grind =]
theorem hasPrefix_append {P : List α → Prop} {l l' : List α} :
    (l ++ l').HasPrefix P ↔ l.HasPrefix P ∨ l'.HasPrefix (fun l'' => P (l ++ l'')) := by
  induction l generalizing P with grind

@[grind =]
theorem sum_append_singleton {α : Type} {l : List α} {x : α}
    [Add α] [Zero α] [@Std.Associative α (· + ·)] [@Std.LawfulIdentity α (· + ·) 0] :
    (l ++ [x]).sum = l.sum + x := by
  induction l with simp_all <;> grind

end List

open Std.Do

set_option mvcgen.warning false

theorem belowZero_iff {l : List Int} : belowZero l ↔ l.HasPrefix (fun l => l.sum < 0) := by
  generalize h : belowZero l = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  -- 早期終了がある場合の不変条件
  · Invariant.withEarlyReturn
    -- 早期終了しなかった場合、現在の接頭辞の和が `balance` に等しく、
    -- かつ「今までループで見てきた部分」は「和が0未満になる接頭辞」を持たない
    (onContinue := fun cursor balance =>
      ⌜balance = cursor.prefix.sum ∧ ¬ cursor.prefix.HasPrefix (fun l => l.sum < 0)⌝)

    -- 早期終了した場合、返り値の`ret`は`true`であり、かつ和が0未満になる接頭辞がある
    (onReturn := fun ret balance => ⌜ret = true ∧ l.HasPrefix (fun l => l.sum < 0)⌝)
  with grind
