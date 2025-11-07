import Lean

open Std.Do

set_option mvcgen.warning false

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

/-- `nodupDo` の結果は標準ライブラリに用意されている `Nodup` と一致する -/
theorem nodup_correct (l : List α) : nodupDo l ↔ l.Nodup := by
  generalize h : nodupDo l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · Invariant.withEarlyReturn
      -- forループの１ステップが平常終了したとき。
      -- プログラム中の可変変数`seen`は、現在までに見た要素の集合`xs.prefix`に等しく、
      -- かつ`xs.prefix`は重複がない。
      (onContinue := fun xs seen => ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
      -- 早期リターンしたとき。
      -- 返り値は`false`であり、かつ`l`に重複がある
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
  with grind
