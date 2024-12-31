/- # exists

`exists` タクティクは、「～を満たす `x` が存在する」という命題を示すために、証拠になる `x` を具体的に示します。

ゴールが `⊢ ∃ x, P x` のとき、`x : X` がローカルコンテキストにあれば、`exists x` によりゴールが `P x` に変わります。同時に、`P x` が自明な場合は証明が終了します。-/
import Lean --#

example : ∃ x : Nat, 3 * x + 1 = 7 := by
  exists 2

/- ## 内部処理についての補足
なお Lean での存在量化の定義は次のようになっています。-/
--#--
-- Exists の定義が変わっていないことを確認する
/--
info: inductive Exists.{u} : {α : Sort u} → (α → Prop) → Prop
number of parameters: 2
constructors:
Exists.intro : ∀ {α : Sort u} {p : α → Prop} (w : α), p w → Exists p
-/
#guard_msgs in #print Exists
--#--
namespace Exists --#

inductive Exists.{u} {α : Sort u} (p : α → Prop) : Prop where
  /-- `a : α` と `h : p a` から `∃ x : α, p x` の証明を得る -/
  | intro (w : α) (h : p w) : Exists p

end Exists --#
/- したがって `Exists` は単一のコンストラクタを持つ[帰納型](../Declarative/Inductive.md)、つまり[構造体](../Declarative/Structure.md)なので、上記の `exists` は `exact` と[無名コンストラクタ](../Declarative/Structure.md#AnonymousConstructor)で次のように書き直すことができます。-/

example : ∃ x : Nat, 3 * x + 1 = 7 := by
  exact ⟨2, show 3 * 2 + 1 = 7 from by rfl⟩

/- 一般に `exists e₁, e₂, .., eₙ` は `refine ⟨e₁, e₂, .., eₙ, ?_⟩; try trivial` の糖衣構文です。-/

/-- `#expand` の入力に渡すための構文カテゴリ -/
syntax macro_stx := command <|> tactic <|> term

open Lean in

/-- マクロを展開するコマンド -/
elab "#expand " t:macro_stx : command => do
  let t : Syntax := match t.raw with
  | .node _ _ #[t] => t
  | _ => t.raw
  match ← Elab.liftMacroM <| Macro.expandMacro? t with
  | none => logInfo m!"Not a macro"
  | some t => logInfo m!"{t}"

/-- info: (refine ⟨1, 2, 3, ?_⟩; try trivial) -/
#guard_msgs in
  #expand exists 1, 2, 3
