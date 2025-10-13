/- # \#guard
`#guard` は与えられた Bool 値が true であることを確かめます。
-/

-- 階乗関数
def fac : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * fac n

#guard fac 5 == 120

/- ## 決定可能性
`#guard` に `Bool` ではなく `Prop` 型の項を与えた場合、エラーになることがあります。次の命題は証明があるので真ですが、 `#guard` は通りません。
-/

example (α : Type) (l : List α) : [] ⊆ l := by simp

-- Prop 型を持つ
#check ((α : Type) → ∀ (l : List α), [] ⊆ l : Prop)

/-⋆-//--
error: Type mismatch
  ∀ (α : Type) (l : List α), [] ⊆ l
has type
  Prop
but is expected to have type
  Bool
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors
-/
#guard_msgs (whitespace := lax) in --#
#guard ((α : Type) → ∀ (l : List α), [] ⊆ l : Prop)

/- しかし、 `1 + 1 = 2` 等も `#check` で確かめてみると型は `Prop` です。にも関わらず `#guard` に渡してもエラーになりません。これは不思議に思えますが、理由は `1 + 1 = 2` が [`Decidable`](#{root}/TypeClass/Decidable.md) 型クラスのインスタンスであり、決定可能だからです。-/

-- 型は Prop
/-⋆-//-- info: 1 + 1 = 2 : Prop -/
#guard_msgs in --#
#check 1 + 1 = 2

#guard 1 + 1 = 2

-- 1 + 1 = 2 は決定可能
#synth Decidable (1 + 1 = 2)

/-
`Prop` 型であっても、`Decidable` クラスのインスタンスであれば `Bool` に変換できます。それを自動で行っているので、`Prop` 型の項でも `#guard` に通せるというわけです。
-/

-- 決定可能な Prop 型の項を Bool に変換する関数
#check (decide : (p : Prop) → [_h : Decidable p] → Bool)

-- Bool 型になっている
/-⋆-//-- info: decide (1 + 1 = 2) : Bool -/
#guard_msgs in --#
#check decide (1 + 1 = 2)

/- ## DIY: 差分の表示

`#guard` コマンドを使って `A = B` という式を評価して `false` だったとき、デフォルトでは `A` と `B` がそれぞれどんな値であるかは表示されません。単に「等しくない」というメッセージが出るだけです。
-/

/-⋆-//--
error: Expression
  decide (1 + 1 = 3)
did not evaluate to `true`
-/
#guard_msgs in --#
#guard 1 + 1 = 3

/- この挙動は少し不便です。`#guard` に渡された等式が `false` だったときに左辺と右辺の値を表示するようなコマンドが欲しいですね。これは、以下のように自作することができます。[^guardDiff]

{{#include ./Guard/GuardDiff.md}}
-/

/-
[^guardDiff]: こちらのコードは Zulip の [#guard with diff](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/.23guard.20with.20diff/with/541898112) というトピックで Marcus Rossel さんによって提案されたコードを参考にしています。
-/
