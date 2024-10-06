/-
# attribute

`attribute` は、属性(attribute)を付与するためのコマンドです。

次の例では、命題に `[simp]` 属性を付与しています。これは `simp` タクティクで利用される命題を増やすことを意味します。
-/
namespace Attribute --#

theorem foo {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  constructor <;> intro h
  · obtain ⟨hPQ, hP⟩ := h
    constructor <;> repeat apply_assumption
  · obtain ⟨hP, hQ⟩ := h
    constructor <;> intros
    all_goals assumption

-- `simp` では示せない
example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  simp
  show P → P ∨ Q

  intro (h : P)
  left
  assumption

-- `attribute` で属性を付与
attribute [simp] foo

-- `simp` で示せるようになった
example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  simp

/- ## 属性の削除
与えた属性を削除することができることもあります。削除するには `-` を属性の頭に付けます。-/
section
  -- `[simp]` 属性を削除
  attribute [-simp] foo

  -- 再び示せなくなった
  example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
    simp
    show P → P ∨ Q

    intro (h : P)
    left
    assumption
end

/- 属性の削除はデバッグを意図した機能で、常にローカルにはたらき、その [`section`](./Section.md) の外に出ると削除された属性が戻ります。-/

example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by simp

/- 属性によっては、削除することができないこともあります。-/

@[irreducible] def greet := "Hello"

/-- error: attribute cannot be erased -/
#guard_msgs in attribute [-irreducible] greet

/- ## タグ
`attribute` コマンドを使用すると定義の後から属性を付与することができますが、定義した直後に属性を付与する場合はタグと呼ばれる `@[..]` という書き方が使えます。-/

@[simp]
theorem bar {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  constructor <;> intro h
  · obtain ⟨hPQ, hP⟩ := h
    constructor <;> repeat apply_assumption
  · obtain ⟨hP, hQ⟩ := h
    constructor <;> intros
    all_goals assumption

example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  simp

/- ## 有効範囲を制限する
特定の [`section`](./Section.md) でのみ付与した属性を有効にするには、[`local`](./Local.md) で属性名を修飾します。
-/
example (P Q : Prop) : ((P ∨ Q) ∧ ¬ Q) ↔ (P ∧ ¬ Q) := by
  -- simp だけでは証明が終わらない
  try simp
  show ¬Q → Q → P

  intro hnQ hQ
  contradiction

section
  -- 補題
  theorem or_and_neg (P Q : Prop) : ((P ∨ Q) ∧ ¬ Q) ↔ (P ∧ ¬ Q) := by
    constructor <;> intro h
    · obtain ⟨hPQ, hnQ⟩ := h
      rcases hPQ with hP | hQ
      · exact ⟨hP, hnQ⟩
      · contradiction
    · obtain ⟨hP, hnQ⟩ := h
      exact ⟨by left; assumption, hnQ⟩

  -- local に simp 補題を登録
  attribute [local simp] or_and_neg

  -- simp で証明ができる
  example (P Q : Prop) : ((P ∨ Q) ∧ ¬ Q) ↔ (P ∧ ¬ Q) := by simp
end

variable (P Q : Prop)

-- section を抜けると simp 補題が利用できない
example (P Q : Prop) : ((P ∨ Q) ∧ ¬ Q) ↔ (P ∧ ¬ Q) := by
  simp

  -- 証明すべきことが残ってしまった
  show ¬Q → Q → P

  intro _ _
  contradiction

end Attribute --#
