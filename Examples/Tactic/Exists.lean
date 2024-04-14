/- # exists

`exists` は，「～という `x` が存在する」という命題を示すために，「この `x` を使え」と指示するコマンドです．

ゴールが `⊢ ∃ x, P x` のとき，`x: X` がローカルコンテキストにあれば，`exists x` によりゴールが `P x` に変わります．同時に，`P x` が自明な場合は証明が終了します．-/

namespace Exists --#

example : ∃ x : Nat, 3 * x + 1 = 7 := by
  exists 2

/- ## 内部処理についての補足
なお Lean での存在量化の定義は次のようになっています．-/

universe u

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  /-- `a : α` と `h : p a` が与えられたとき `∃ x : α, p x` が成り立つ. -/
  | intro (w : α) (h : p w) : Exists p

/- したがって上記の `exists` は `exact` で次のように書き直すことができます．-/

example : ∃ x : Nat, 3 * x + 1 = 7 := by
  exact ⟨2, show 3 * 2 + 1 = 7 from by rfl⟩

/- 一般に `exists e₁, e₂, ..` は `refine ⟨e₁, e₂, ..⟩; try trivial` の糖衣構文です．-/

end Exists --#
