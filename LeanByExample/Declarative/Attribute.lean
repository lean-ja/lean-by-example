/-
# attribute

`attribute` は、属性(attribute)を付与するためのコマンドです。

次の例では、命題に `[simp]` 属性を付与しています。これは `simp` タクティクで利用される命題を増やすことを意味します。
-/

theorem foo {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  constructor <;> intro h
  all_goals
    refine ⟨?_, by simp_all⟩
    simp_all

#guard_msgs (drop warning) in --#
example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  -- `simp` では示せない
  fail_if_success solve
  | simp

  sorry

-- `attribute` で属性を付与
attribute [simp] foo

example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  -- `simp` で示せるようになった
  simp

/- ## 属性の削除
与えた属性を削除することができることもあります。削除するには `-` を属性の頭に付けます。属性の削除はデバッグを意図した機能で、常にローカルにはたらき、その[セクション](./Section.md)の外に出ると削除された属性が戻ります。-/
section
  -- `[simp]` 属性を削除
  attribute [-simp] foo

  -- 再び `simp` では示せなくなった
  #guard_msgs (drop warning) in --#
  example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
    fail_if_success solve
    | simp

    sorry
end

-- `simp` で示せるようになった
example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by simp

/- 属性によっては、削除することができないこともあります。-/

@[irreducible] def greet := "Hello"

/-⋆-//-- error: attribute cannot be erased -/
#guard_msgs in --#
attribute [-irreducible] greet

/- ## タグ
`attribute` コマンドを使用すると定義の後から属性を付与することができますが、定義した直後に属性を付与する場合はタグと呼ばれる `@[..]` という書き方が使えます。-/

@[simp]
theorem bar {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  constructor <;> intro h
  all_goals
    refine ⟨?_, by simp_all⟩
    simp_all

example {P Q : Prop} : (P → Q) ∧ P ↔ Q ∧ P := by
  simp

/- ## 有効範囲を制限する
特定の [`section`](./Section.md) 内でのみ付与した属性を有効にするには、[`local`](#{root}/Modifier/Local.md) で属性名を修飾します。
-/
#guard_msgs (drop warning) in --#
example (P Q : Prop) : ((P ∨ Q) ∧ ¬ Q) ↔ (P ∧ ¬ Q) := by
  -- simp だけでは証明できない
  fail_if_success solve
  | simp

  sorry

section
  -- 補題
  theorem or_and_neg (P Q : Prop) : ((P ∨ Q) ∧ ¬ Q) ↔ (P ∧ ¬ Q) := by
    constructor <;> intro h
    · refine ⟨?_, by simp_all⟩
      have : ¬ Q := h.right
      simp_all
    · refine ⟨?_, by simp_all⟩
      simp_all

  -- local に simp 補題を登録
  attribute [local simp] or_and_neg

  -- simp で証明ができるようになった！
  example (P Q : Prop) : ((P ∨ Q) ∧ ¬ Q) ↔ (P ∧ ¬ Q) := by simp
end

#guard_msgs (drop warning) in --#
example (P Q : Prop) : ((P ∨ Q) ∧ ¬ Q) ↔ (P ∧ ¬ Q) := by
  -- section を抜けると simp 補題が利用できなくなった
  fail_if_success solve
  | simp

  sorry
