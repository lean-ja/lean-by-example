import Lean

open Std

/-- `twoSum`関数を関数型スタイルで書き直したもの -/
def twoSum (nums : List Int) (target : Int) : Option (Nat × Nat) :=
  let rec loop (xs : List Int) (i : Nat) (seen : HashMap Int Nat) : Option (Nat × Nat) :=
    match xs with
    | [] => none
    | n :: rest =>
      let diff := target - n
      match seen.get? diff with
      | some j => some (j, i)
      | none => loop rest (i + 1) (seen.insert n i)
  loop nums 0 {}

variable (nums : List Int) (target : Int)

@[simp, grind =]
theorem twoSum_nil : twoSum [] target = none := by
  rfl

/-- 辞書にものを挿入した後で取り出すと、取り出される。

当たり前の補題（当たり前のことが示せることを確認している）。
しかし `EquivBEq` や `LawfulHashable` のインスタンスが必要なことを忘れてはいけない。
-/
@[simp, grind =]
theorem HashMap_get?_insert_eq {α β : Type} [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
  (m : HashMap α β) (a : α) (b : β) :
  (m.insert a b).get? a = some b := by simp

set_option warn.sorry false

theorem twoSum_loop_indices_increasing
  (xs : List Int) (k : Nat) (seen : HashMap Int Nat) (i j : Nat) :
  twoSum.loop target xs k seen = some (i, j) → i < j := by
  induction xs.length with
  | zero => sorry
  | succ n ih => sorry

theorem twoSum_distinct (i j : Nat) :
    twoSum nums target = some (i, j) → i < j := by
  intro h
  induction nums with
  | nil => simp_all
  | cons n rest ih =>
    simp [twoSum, twoSum.loop] at h
    sorry
