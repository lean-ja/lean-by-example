/- # add_aesop_rules
`add_aesop_rules` は [`aesop`](../Tactic/Aesop.md) タクティクに追加のルールを登録するためのコマンドです。-/
import Aesop

/-- 自然数 n が正の数であることを表す命題 -/
inductive Pos : Nat → Prop
  | succ n : Pos (n + 1)

example : Pos 1 := by
  -- 最初はルールが足りなくて示せない
  fail_if_success aesop

  -- 手動でコンストラクタを `apply` することで証明できる
  apply Pos.succ

-- `Pos` 関連のルールを `aesop` に憶えさせる
add_aesop_rules safe constructors [Pos]

-- aesop で示せる
example : Pos 1 := by aesop

/-
`add_aesop_rules` は、`add_aesop_rules (phase)? (priority)? (builder)? [(rule_sets)?]` という構文で使用できます。

## phase について

`phase` は `norm` と `safe` と `unsafe` の３通りです。ルールが適用される順番などに影響します。

### norm

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

-- aesop に登録する
add_aesop_rules norm simp [erase_duplicate]

example (P : Prop) (hp : P) : MyAnd P P := by
  -- aesop で証明できるようになった!
  aesop

/- ### safe

`safe` ルールは、`norm` ルールの実行後に適用されます。あるゴールが証明可能であるとき、それに `safe` ルールを適用しても生成されるゴールは依然として証明可能であるように、`safe` ルールを選ぶことが推奨されます。
-/
section --#

/-- 自前で定義したリスト -/
inductive MyList (α : Type)
  | nil
  | cons (head : α) (tail : MyList α)

/-- リストが空ではないことを表す述語 -/
inductive NonEmpty {α : Type} : MyList α → Prop
  | cons x xs : NonEmpty (MyList.cons x xs)

local add_aesop_rules safe apply [NonEmpty.cons]

-- aesop で `NonEmpty _` という形のゴールを示せる
example : NonEmpty (MyList.cons 1 MyList.nil) := by aesop

end --#
/- ### unsafe
`unsafe` ルールは、すべての `safe` ルールが失敗した場合に適用されます。失敗したらバックトラックして他の `unsafe` ルールを試します。`priority` として成功する確率(%)を指定する必要があります。
-/
section --#

-- 推移律を `unsafe` ルールとして登録する
local add_aesop_rules unsafe 10% apply [Nat.le_trans]

example (a b c d e : Nat)
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) : a ≤ e := by
  -- aesop で証明できるようになった！
  aesop

end --#
/- `safe` ルールは常に適用されてしまうため、特定の状況でのみ適用したいルールは `unsafe` とすることが推奨されます。誤って `safe` ルールに登録してしまうと上手く動作しないことがあります。 -/
section --#

-- safe ルールとして推移律を登録する
local add_aesop_rules safe apply [Nat.le_trans]

example (a b c d e : Nat)
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) : a ≤ e := by
  -- aesop で証明できない
  fail_if_success aesop

  calc
    a ≤ b := by assumption
    _ ≤ c := by assumption
    _ ≤ d := by assumption
    _ ≤ e := by assumption

end --#
/- ## builder について
`builder` には多くの選択肢があります。ここではその一部を紹介します。

### apply

`apply` タクティクと同様にはたらくルールを登録します。
-/
section --#

example (a b c d e : Nat)
    (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) : a < e := by
  -- 最初は aesop で示せない
  fail_if_success aesop

  -- 手動で示すならこのように apply を繰り返すことになる
  apply Nat.lt_trans (m := d) <;> try assumption
  apply Nat.lt_trans (m := c) <;> try assumption
  apply Nat.lt_trans (m := b) <;> try assumption

-- 推移律を登録する
local add_aesop_rules unsafe 10% apply [Nat.lt_trans]

example (a b c d e : Nat)
    (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) : a < e := by
  -- aesop で証明できるようになった
  aesop

end --#
/- ### constructors
`constructors` ビルダーは、[帰納型](../Declarative/Inductive.md) `T` の形をしたゴールに遭遇した際に、コンストラクタを適用するように指示します。
-/
section --#

/-- 自前で定義した偶数を表す命題 -/
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
local add_aesop_rules safe constructors [Even]

example : Even 2 := by
  -- aesop で証明できるようになった
  aesop

end --#
/- ### cases
`cases` ビルダーは、帰納型 `T` の形をした仮定がローカルコンテキストにある場合に、それに対して再帰的に `cases` タクティクを使用して分解するように指示します。
-/
section --#

example (n : Nat) (h : Even (n + 2)) : Even n := by
  -- 最初は aesop で証明できない
  fail_if_success aesop

  -- 手動で cases を使って分解することで証明できる
  cases h
  assumption

-- aesop にルールを登録する
local add_aesop_rules safe cases [Even]

example (n : Nat) (h : Even (n + 2)) : Even n := by
  -- aesop で証明できるようになった
  aesop

end --#
/- ### destruct
`destruct` ビルダーは、`A₁ → ⋯ → Aₙ → B` という形の命題を登録することで、仮定に `A₁, ..., Aₙ` が含まれている場合に、元の仮定を消去して `B` を仮定に追加します。
-/
section --#

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

example {n : Nat} : Even n ∨ Even (n + 1) := by
  -- 最初は aesop で証明できない
  fail_if_success aesop

  -- 手動で補題を示すことで証明する
  have := even_or_even_succ n
  assumption

local add_aesop_rules unsafe 30% destruct [even_or_even_succ]

example {n : Nat} : Even n ∨ Even (n + 1) := by
  -- aesop で示せるようになった！
  aesop

end --#
/- ### tactic
`tactic` ビルダーは、タクティクを追加のルールとして直接利用できるようにします。
-/
section --#

example (a b : Nat) (h : 3 ∣ (10 * a + b)) : 3 ∣ (a + b) := by
  -- aesop で証明できない
  fail_if_success aesop

  -- omega で証明できる
  omega

-- aesop にルールを登録する
add_aesop_rules safe tactic [(by omega)]

example (a b : Nat) (h : 3 ∣ (10 * a + b)) : 3 ∣ (a + b) := by
  -- aesop で証明できるようになった!
  aesop
end --#
