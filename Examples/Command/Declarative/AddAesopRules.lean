/- # add_aesop_rules
`add_aesop_rules` は [`aesop`](../../Tactic/Aesop.md) タクティクに追加のルールを登録するためのコマンドです。-/
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
## 構文

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

/-- 自前で定義したリスト -/
inductive MyList (α : Type)
  | nil
  | cons (head : α) (tail : MyList α)

/-- リストが空ではないことを表す述語 -/
inductive NonEmpty {α : Type} : MyList α → Prop
  | cons x xs : NonEmpty (MyList.cons x xs)

add_aesop_rules safe apply [NonEmpty.cons]

-- aesop で `NonEmpty _` という形のゴールを示せる
example : NonEmpty (MyList.cons 1 MyList.nil) := by aesop

/- ### unsafe
`unsafe` ルールは、すべての `safe` ルールが失敗した場合に適用されます。失敗したらバックトラックして他の `unsafe` ルールを試します。`priority` として成功する確率(%)を指定する必要があります。

`safe` ルールは常に適用されてしまうため、特定の状況でのみ適用したいルールは `unsafe` とすることが推奨されます。
-/
section

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

end
section

-- 推移律を今度は unsafe ルールとして登録する
local add_aesop_rules unsafe 10% apply [Nat.le_trans]

example (a b c d e : Nat)
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) : a ≤ e := by
  -- aesop で証明できる
  aesop

end
