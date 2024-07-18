/- # \#print
`#print` コマンドには複数の機能がありますが、単体で使うと定義を表示することができます。
-/
import Lean --#

/--
info: inductive Or : Prop → Prop → Prop
number of parameters: 2
constructors:
Or.inl : ∀ {a b : Prop}, a → a ∨ b
Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/
#guard_msgs in #print Or

/--
info: theorem Nat.add_succ : ∀ (n m : Nat), n + m.succ = (n + m).succ :=
fun n m => rfl
-/
#guard_msgs in #print Nat.add_succ

/-!
## 依存公理を確認

`#print axioms` で、与えられた証明項が依存する公理を出します。たとえば Lean では排中律は選択原理 `Classical.choice` (選択公理の Lean 版のようなもの)を使って証明するので、排中律は選択原理に依存しています。
-/

/-- 排中律 -/
example : ∀ (p : Prop), p ∨ ¬p := Classical.em

/-- info: 'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Classical.em

/-! また、`sorry` という命題を「証明したことにする」タクティクがありますが、これは `sorryAx` という万能な公理を導入していることが確認できます。-/

theorem contra : False := by sorry

/-- info: 'contra' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms contra

/- ## よくあるエラー
`#print` コマンドは式ではなく名前を受け付けます。たとえば、`#print Nat.zero` はエラーになりませんが、`#print Nat.succ Nat.zero` はエラーになります。この挙動は `#eval` コマンドや `#check` コマンドとは異なるため、注意が必要です。
-/

open Lean

/--
error: application type mismatch
  a.raw
argument
  a
has type
  TSyntax `term : Type
but is expected to have type
  TSyntax [`ident, `str] : Type
-/
#guard_msgs(error) in
#eval show Lean.Elab.Term.TermElabM Unit from do
  let a ← `(Nat.succ Nat.zero)
  let _b ← `(#print $a)

/- 上のコード例は、これを検証するものです。エラーメッセージにあるように `#print` は `ident` または `str` を期待しており、これはそれぞれ単一の識別子と文字列リテラルを意味します。`Nat.succ Nat.zero` は `term` つまり項なのでエラーになります。

`#check` や `#eval` の場合は項を受け付けるので、エラーになりません。-/

#eval show Lean.Elab.Term.TermElabM Unit from do
  let a ← `(Nat.succ Nat.zero)
  let _b ← `(#eval $a)

#eval show Lean.Elab.Term.TermElabM Unit from do
  let a ← `(Nat.succ Nat.zero)
  let _b ← `(#check $a)
