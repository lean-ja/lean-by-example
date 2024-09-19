/- # Decidable
`Decidable` は、命題が決定可能であることを示す型クラスです。

ここで命題 `P : Prop` が決定可能であるとは、その真偽を決定するアルゴリズムが存在することを意味します。具体的には `P : Prop` が `Decidable` のインスタンスであるとき、`decide` 関数を適用することにより `decide P : Bool` が得られます。
-/
namespace Decidable --#

-- 決定可能な命題を決定する関数 decide が存在する
#check (decide : (P : Prop) → [Decidable P] → Bool)

/-- info: true -/
#guard_msgs in #eval decide (2 + 2 = 4)

/-- info: false -/
#guard_msgs in #eval decide (2 + 2 = 5)

/- `Decidable` 型クラスのインスタンスに対しては、[`decide`](../Tactic/Decide.md) タクティクにより証明が可能です。 -/

/-- 自前で定義した偶数を表す述語 -/
def Even (n : Nat) : Prop := ∃ m : Nat, n = 2 * m

/-- Even が決定可能であることを示す -/
instance (n : Nat) : Decidable (Even n) := by
  -- n % 2 の計算に帰着させる
  refine decidable_of_iff (n % 2 = 0) ?_

  -- 以下の同値性を示せばよい
  dsimp [Even]
  show n % 2 = 0 ↔ ∃ m, n = 2 * m

  constructor <;> intro h

  -- 左から右を示す
  case mp =>
    exists (n / 2)
    omega

  -- 右から左を示す
  case mpr =>
    obtain ⟨m, rfl⟩ := h
    omega

-- decide で証明ができるようになる
example : Even 4 := by decide

/- ## class inductive
`Decidable` 型クラスの定義は少し特殊です。コンストラクタが複数あり、構造体ではなく帰納型の構造をしています。これは `Decidable` が [`class inductive`](../Declarative/Class.md#ClassInductive) というコマンドで定義されているためです。-/

/--
info: inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
-/
#guard_msgs in #print Decidable

end Decidable --#
