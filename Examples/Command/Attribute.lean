/-
# attribute

`attribute` は，属性(attribute)を付与するためのコマンドです．

次の例では，命題に `simp` 属性を付与しています．これは `simp` タクティクで利用される命題を増やすことを意味します．
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

/- 属性によっては与えた属性を削除することもできます．削除するには `-` を属性の頭に付けます．-/

-- `simp` 属性を削除
attribute [-simp] foo

-- 再び示せなくなった
example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  simp
  show P → P ∨ Q

  intro (h : P)
  left
  assumption

/- `attribute` コマンドを使用すると定義の後から属性を付与することができますが，定義した直後に属性を付与する場合はタグと呼ばれる `@[..]` という書き方が使えます．-/

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

end Attribute --#
