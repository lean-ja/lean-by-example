/- # use

`use` タクティクは、「～を満たす `x` が存在する」という命題を示すために、証拠になる `x` を具体的に示します。

ゴールが `⊢ ∃ x, P x` のとき、`x : X` がローカルコンテキストにあれば、`use x` によりゴールが `⊢ P x` に変わります。同時に、`P x` が自明な場合は証明が終了します。
-/
import Mathlib.Tactic.Use
import Mathlib.Tactic.Linarith
set_option warn.sorry false --#

example {α : Type} (P : α → Prop) (x : α) : ∃ y, P y := by
  use x
  -- ゴールが `P x` に変わる
  guard_target =ₛ P x

  sorry

/- ## exists との違い
これだけの説明だと [`exists`](./Exists.md) タクティクと同じに見えますが、`use` タクティクには `exists` より優れている点があります。

### discharger が指定できる
`use` は、証拠を与えた後にゴールを閉じるために使うタクティク（`discharger` と呼ばれます）を指定することができます。
-/

example (x : Rat) (h : 3 * x + 6 > 6) : ∃ (y : Rat), y > 0 := by
  exists x
  linarith

example (x : Rat) (h : 3 * x + 6 > 6) : ∃ (y : Rat), y > 0 := by
  -- `discharger` として `linarith` を指定することができる
  use (discharger := linarith) x

/- `exists` タクティクにこの構文は存在しません。-/

open Lean Parser in

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

-- `exists (discharger := linarith)` と書くとパースエラーになる
/-⋆-//-- error: <input>:1:19: expected ')', ',' or ':' -/
#guard_msgs in --#
#eval parse `tactic "exists (discharger := linarith) 1"

/- ### Exists 以外の型にも使用できる
`exists` は、ゴールの型が `Exists` であるという想定をしているため、たとえばフィールドの数が３以上であるような構造体に対して使うとエラーになります。
-/

/-- 例示のための構造体。フィールドの数が `Exists` より多い -/
structure Foo where
  x : Int
  pos : x > 0
  sq : x ^ 2 = 9

/-- `Foo` の項を具体的に与える例 -/
example : Foo := ⟨3, by simp, by simp⟩

/-⋆-//--
error: invalid constructor ⟨...⟩, insufficient number of arguments, constructs 'Foo.mk' has #3 explicit fields, but only #2 provided
-/
#guard_msgs in --#
example : Foo := by
  exists 3

/- しかし、`use` タクティクであれば対応することができます。 -/

example : Foo := by
  -- 最初のフィールドを `3` で埋めるように指示する
  use 3

  -- 残りのフィールドは `simp` で証明することができる
  all_goals simp

example : Foo := by
  -- `discharger` を指定するバージョン
  use (discharger := simp) 3
