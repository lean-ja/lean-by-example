import Lean

open Std.WP

variable {α : Type} [Hashable α] [DecidableEq α]

/-- リストに重複がないか判定する。
true なら重複がない。false なら重複がある。-/
def nodupDo (l : List α) : Bool := Id.run do
  let mut seen : Std.HashSet α := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

-- `vcgen` は実験的機能だよという警告を消す
set_option experimental.vcgen true in

/-- `nodupDo` の結果は標準ライブラリに用意されている `Nodup` と一致する -/
theorem nodup_correct (l : List α) : nodupDo l ↔ l.Nodup := by
  generalize h : nodupDo l = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · Invariant.withEarlyReturnNewDo Prop
    -- forループの１ステップが平常終了したとき。
    -- プログラム中の可変変数`seen`は、現在までに見た要素の集合`pref`に等しく、
    -- かつ`pref`は重複がない。
    (onContinue := fun pref _ (seen : Std.HashSet α) =>
      (∀ x, x ∈ seen ↔ x ∈ pref) ∧ pref.Nodup)
    -- 早期リターンしたとき。
    -- 返り値は`false`であり、かつ`l`に重複がある
    (onReturn := fun ret _ => ret = false ∧ ¬l.Nodup)
  all_goals simp_all <;> grind
