/- # with_reducible

[`🏷️メタプログラミング`](./?search=🏷メタプログラミング)

`with_reducible` は、後に続くタクティクの透過度(transparency)を `reducible` に指定して実行します。透過度 `reducible` では、`[reducible]` 属性を持つ定義だけが展開されます。

## 用途

`with_reducible` はタクティクを定義するマクロを書く際に有用です。推移律を利用して、不等式を分割するタクティクを定義する例を示しましょう。

まず、不等式の推移律を使う証明の例を示します。
-/

variable (a b c : Nat)

example (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  -- b を経由して示す
  apply Nat.le_trans (m := b) <;> assumption

example (h₁ : a < b) (h₂ : b < c) : a < c := by
  -- b を経由して示す
  apply Nat.lt_trans (m := b) <;> assumption

/- 今からすることは、この２つの命題を１つのタクティクで証明できるようにすることです。コードを素直に共通化しようとして次のようにマクロを定義すると上手くいきません。-/
section --#
/-- 推移律を扱うタクティク -/
syntax "my_trans" term : tactic

-- `<` に対するルール
local macro_rules
  | `(tactic| my_trans $e) => `(tactic| apply Nat.lt_trans (m := $e))

-- `≤` に対するルール
local macro_rules
  | `(tactic| my_trans $e) => `(tactic| apply Nat.le_trans (m := $e))

example (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  -- 成功
  my_trans b <;> assumption

example (h₁ : a < b) (h₂ : b < c) : a < c := by
  -- 失敗
  my_trans b <;> try assumption

  exact Nat.le_of_succ_le h₂

end --#
/- マクロ展開のルールとして、Lean は後に定義されたルールを先に適用するので、常に `Nat.le_trans` を先に適用します。ところが `<` は `≤` を使って定義されているため、`<` に対しても `apply Nat.le_trans` が成功してしまいます。その結果、`<` に対して `Nat.lt_trans` を使ってくれないという結果になっています。-/

/-- `<` は `≤` を使って定義されている -/
example (n m : Nat) : (Nat.lt n m) = (Nat.le n.succ m) := rfl

example (h₁ : a < b) (h₂ : b < c) : a < c := by
  -- < に対しても Nat.le_trans が成功してしまう
  apply Nat.le_trans (m := b)
  · exact h₁
  · exact Nat.le_of_succ_le h₂

/- `with_reducible` を使用すると、`[reducible]` とマークされていない定義は展開されなくなるので、この挙動を防ぐことができます。 -/

example (h₁ : a < b) (h₂ : b < c) : a < c := by with_reducible
  -- < に対して Nat.le_trans が成功しなくなった！
  fail_if_success apply Nat.le_trans (m := b)

  apply Nat.lt_trans (m := b) <;> assumption

section --#

-- `<` に対するルール
local macro_rules
  | `(tactic| my_trans $e) => `(tactic| with_reducible apply Nat.lt_trans (m := $e))

-- `≤` に対するルール
local macro_rules
  | `(tactic| my_trans $e) => `(tactic| with_reducible apply Nat.le_trans (m := $e))

example (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  -- 成功
  my_trans b <;> assumption

example (h₁ : a < b) (h₂ : b < c) : a < c := by
  -- 成功
  my_trans b <;> try assumption

end --#
