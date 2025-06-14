/- # Decidable
`Decidable` は、命題が決定可能であることを示す型クラスです。

ここで命題 `P : Prop` が決定可能であるとは、その真偽を決定するアルゴリズムが存在することを意味します。具体的には `P : Prop` が `Decidable` のインスタンスであるとき、`decide` 関数を適用することにより `decide P : Bool` が得られます。
-/

-- 決定可能な命題を決定する関数 decide が存在する
#check (decide : (P : Prop) → [Decidable P] → Bool)

/-⋆-//-- info: true -/
#guard_msgs in --#
#eval decide (2 + 2 = 4)

/-⋆-//-- info: false -/
#guard_msgs in --#
#eval decide (2 + 2 = 5)

/- `Decidable` 型クラスのインスタンスに対しては、[`decide`](#{root}/Tactic/Decide.md) タクティクにより証明が可能です。 -/

/-- 自前で定義した偶数を表す述語 -/
def Even (n : Nat) : Prop := ∃ m : Nat, n = 2 * m

example : Even 4 := by
  -- 最初は decide で示すことができない
  fail_if_success decide

  exists 2

theorem even_impl (n : Nat) : n % 2 = 0 ↔ Even n := by
  constructor <;> intro h
  case mp =>
    exists (n / 2)
    omega
  case mpr =>
    obtain ⟨m, rfl⟩ := h
    omega

/-- Even が決定可能であることを示す -/
instance (n : Nat) : Decidable (Even n) :=
  decidable_of_iff (n % 2 = 0) (even_impl n)

-- decide で証明ができるようになった！
example : Even 4 := by decide

/- ## class inductive
`Decidable` 型クラスの定義は少し特殊です。コンストラクタが複数あり、[構造体](#{root}/Declarative/Structure.md)ではなく[帰納型](#{root}/Declarative/Inductive.md)の構造をしています。これは `Decidable` が [`class inductive`](#{root}/Declarative/Class.md#ClassInductive) というコマンドで定義されているためです。-/

namespace Hidden --#
--#--
-- Decidable の定義が変わっていないことを確認する
/--
info: inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
-/
#guard_msgs in #print Decidable
--#--

class inductive Decidable (p : Prop) where
  /-- `¬ p` であることが分かっているなら、`p` は決定可能 -/
  | isFalse (h : Not p) : Decidable p
  /-- `p` であることが分かっているなら、`p` は決定可能 -/
  | isTrue (h : p) : Decidable p
end Hidden --#
