/- # aesop

`[aesop]` は [`aesop`](#{root}/Tactic/Aesop.md) タクティクに追加のルールを登録するための属性です。同様の機能を持つコマンドに [`add_aesop_rules`](#{root}/Declarative/AddAesopRules.md) があります。 -/
import Aesop

/-- 自然数 n が正の数であることを表す帰納的述語 -/
inductive Pos : Nat → Prop where
  | succ n : Pos (n + 1)

example : Pos 1 := by
  -- 最初はルールが足りなくて示せない
  fail_if_success aesop

  -- 手動でコンストラクタを `apply` することで証明できる
  apply Pos.succ

-- `Pos` 関連のルールを `aesop` に憶えさせる
attribute [aesop safe constructors] Pos

-- aesop で示せるようになった！
example : Pos 1 := by aesop

/-
なお `aesop` をカスタマイズしたものを専用のタクティクにまとめることも可能ですが、それについてはここでは詳しく述べません。[`declare_aesop_rule_sets`](#{root}/Declarative/DeclareAesopRuleSets.md) コマンドのページを参照してください。

`[aesop]` 属性は、`[aesop <phase>? <priority>? <builder_name>? <builder_option>? <rule_sets>?]` という構文で使用できます。

## phase について

`phase` は `norm` と `safe` と `unsafe` の３通りです。「ルールを適用した後、ダメそうだとわかったら引き返せ」「常に最初に適用せよ」など試行錯誤のやり方を指示します。-/

open Lean Parser Category in

-- `Aesop.phase` という構文カテゴリが存在する
#check (Aesop.phase : Category)

/- ### norm

`norm` は正規化(normalisation)ルールを表します。最初に適用されるルール群であり、適用によりゴールが増えないようなルールだけを登録することが推奨されます。`[simp]` 補題と同様に使用されます。
-/

/-- And を模倣して自作した型 -/
structure MyAnd (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

/-- `P ∧ P ↔ P` に相当するルール -/
theorem erase_duplicate {P : Prop} : MyAnd P P ↔ P := by
  constructor <;> intro h
  · rcases h with ⟨h⟩
    exact h
  · exact MyAnd.intro h h

#guard_msgs (drop warning) in --#
example (P : Prop) (hp : P) : MyAnd P P := by
  -- 最初は aesop で証明できない
  fail_if_success solve
  | aesop
  sorry

-- aesop に登録する
attribute [aesop norm simp] erase_duplicate

example (P : Prop) (hp : P) : MyAnd P P := by
  -- aesop で証明できるようになった!
  aesop

/- ### safe

`safe` ルールは、`norm` ルールの実行後に適用されます。あるゴールが証明可能であるとき、それに `safe` ルールを適用しても生成されるゴールは依然として証明可能であるように、`safe` ルールを選ぶことが推奨されます。
-/
section --#

/-- 自前で定義したリスト -/
inductive MyList (α : Type) where
  | nil
  | cons (head : α) (tail : MyList α)

/-- リストが空ではないことを表す帰納的述語 -/
inductive NonEmpty {α : Type} : MyList α → Prop where
  | cons x xs : NonEmpty (MyList.cons x xs)

#guard_msgs (drop warning) in --#
example : NonEmpty (MyList.cons 1 MyList.nil) := by
  -- 最初は aesop で証明できない
  fail_if_success aesop
  sorry

attribute [aesop safe apply] NonEmpty.cons

-- aesop で示せるようになった！
example : NonEmpty (MyList.cons 1 MyList.nil) := by aesop

end --#
/- ### unsafe
`unsafe` ルールは、すべての `safe` ルールが失敗した場合に適用されます。失敗したらバックトラックして他の `unsafe` ルールを試します。`priority` として成功する確率(%)を指定する必要があります。
-/
section --#

variable (a b c d e : Nat)

#guard_msgs (drop warning) in --#
example (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) : a ≤ e := by
  -- 最初は aesop で証明できない
  fail_if_success aesop
  sorry

-- 推移律を `unsafe` ルールとして登録する
attribute [local aesop unsafe 10% apply] Nat.le_trans

example (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) : a ≤ e := by
  -- aesop で証明できるようになった！
  aesop

end --#
/- `safe` ルールは適用すると後戻りができないため、特定の状況でのみ適用したいルールは `unsafe` とすることが推奨されます。誤って `safe` ルールに登録してしまうと上手く動作しないことがあります。 -/
section --#

-- 同じ推移律を今度は `safe` ルールとして登録する
attribute [local aesop safe apply] Nat.le_trans

variable (a b c d e : Nat)

#guard_msgs (drop warning) in --#
example (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) : a ≤ e := by
  -- aesop で証明できない
  -- 同じ命題を同じように登録したが、safe にしてしまったからダメだった
  fail_if_success aesop

  sorry

end --#
/- ## builder_name について
`builder_name` は、登録されるルールに対して「ゴールを分解する」「仮定から推論を進める」といった方向性を決めます。複数の選択肢がありますが、ここではその一部を紹介します。-/

open Lean Parser Category in

-- `Aesop.builder_name` という構文カテゴリが存在する
#check (Aesop.builder_name : Category)

/- ### apply

`apply` タクティクと同様にはたらくルールを登録します。
-/
section --#

variable (a b c d e : Nat)

example (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) : a < e := by
  -- 最初は aesop で示せない
  fail_if_success aesop

  -- 手動で示すならこのように apply を繰り返すことになる
  apply Nat.lt_trans (m := d) <;> try assumption
  apply Nat.lt_trans (m := c) <;> try assumption
  apply Nat.lt_trans (m := b) <;> try assumption

-- 推移律を登録する
attribute [aesop unsafe 10% apply] Nat.lt_trans

example (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) : a < e := by
  -- aesop で証明できるようになった!
  aesop

end --#
/- ### constructors
`constructors` ビルダーは、[帰納型](#{root}/Declarative/Inductive.md) `T` の形をしたゴールに遭遇した際に、コンストラクタを適用するように指示します。
-/
section --#

/-- 自前で定義した偶数を表す帰納的述語 -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ m : Even m → Even (m + 2)

example : Even 2 := by
  -- 最初は aesop で証明できない
  fail_if_success aesop

  -- 手動でコンストラクタを適用することで示せる
  apply Even.succ
  apply Even.zero

-- aesop にルールを登録する
attribute [aesop safe constructors] Even

example : Even 2 := by
  -- aesop で証明できるようになった!
  aesop

end --#
/- ### cases
`cases` ビルダーは、帰納型 `T` の形をした仮定がローカルコンテキストにある場合に、それに対して再帰的に `cases` タクティクを使用して分解するように指示します。
-/
section --#

/-- 自前で定義した奇数を表す帰納的述語 -/
inductive Odd : Nat → Prop where
  | one : Odd 1
  | succ m : Odd m → Odd (m + 2)

example (n : Nat) (h : Odd (n + 2)) : Odd n := by
  -- 最初は aesop で証明できない
  fail_if_success aesop

  -- 手動で cases を使って分解することで証明できる
  cases h
  assumption

-- aesop にルールを登録する
attribute [aesop safe cases] Odd

example (n : Nat) (h : Odd (n + 2)) : Odd n := by
  -- aesop で証明できるようになった
  aesop

end --#
/- ### destruct
`destruct` ビルダーは、`A₁ → ⋯ → Aₙ → B` という形の命題を登録することで、仮定に `A₁, ..., Aₙ` が含まれている場合に、元の仮定を消去して `B` を仮定に追加します。
-/
namespace destruct --#

/-- 自前で定義した偶数を表す帰納的述語 -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ m : Even m → Even (m + 2)

/-- 任意の数 n について、n か n + 1 のどちらかは偶数 -/
theorem even_or_even_succ (n : Nat) : Even n ∨ Even (n + 1) := by
  induction n with
  | zero => left; apply Even.zero
  | succ n ih =>
    rcases ih with ih | ih
    · right
      apply Even.succ
      assumption
    · left
      assumption

example {n : Nat} (h0 : ¬ Even n) (h1 : ¬ Even (n + 1)) : False := by
  -- 最初は aesop で証明できない
  fail_if_success aesop

  -- 手動で補題を示すことで証明する
  have := even_or_even_succ n
  simp_all

attribute [aesop unsafe 30% destruct] even_or_even_succ

example {n : Nat} (h0 : ¬ Even n) (h1 : ¬ Even (n + 1)) : False := by
  -- aesop で示せるようになった！
  aesop

end destruct --#
/- ### tactic
`tactic` ビルダーは、タクティクを追加のルールとして直接利用できるようにします。
-/
section --#

example (a b : Nat) (h : 3 ∣ (10 * a + b)) : 3 ∣ (a + b) := by
  -- aesop で証明できない
  fail_if_success aesop

  -- omega を使えば証明できる
  omega

open Lean Elab Tactic in

-- aesop にルールを登録する
attribute [aesop safe tactic] Omega.omegaDefault

example (a b : Nat) (h : 3 ∣ (10 * a + b)) : 3 ∣ (a + b) := by
  -- aesop で証明できるようになった!
  aesop
end --#
/- ただし `tactic` ビルダーは受け入れる型が少し特殊で、`TacticM Unit` などの少数の型の項しか受け入れません。正確にどの型の項を受け入れるかは、エラーメッセージで確認できます。-/

/--
error: aesop: tactic builder: expected foo to be a tactic, i.e. to have one of these types:
  TacticM Unit
  SimpleRuleTac
  RuleTac
  TacGen
However, it has type
  String
-/
#guard_msgs in
  @[aesop safe tactic] def foo := "hello"
