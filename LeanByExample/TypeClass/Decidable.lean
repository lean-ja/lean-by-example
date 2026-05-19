/- # Decidable
`Decidable` は、命題が決定可能であることを示す型クラスです。

ここで命題 `P : Prop` が決定可能であるとは、（後述する例外を除き）その真偽を決定するアルゴリズムが存在することを意味します。具体的には `P : Prop` が `Decidable` のインスタンスであるとき、`decide` 関数を適用することにより `decide P : Bool` が得られます。
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

/- `Decidable` を構築する典型的な方法として、`Bool` に帰着する方法があります。-/
theorem decidable_of_bool_iff (P : Prop) (comp : Bool) (h : comp = true ↔ P) : Decidable P := by
  cases hc : comp with
  | false =>
    apply Decidable.isFalse
    intro hp
    have : false = true := by simpa [hc] using h.mpr hp
    contradiction
  | true =>
    apply Decidable.isTrue
    exact h.mp (by simpa [hc])

/-- Even を判定する計算 -/
def evenComp (n : Nat) : Bool := decide (n % 2 = 0)

theorem evenComp_spec (n : Nat) : evenComp n = true ↔ Even n := by
  exact Iff.trans (by simpa [evenComp] using (decide_eq_true_eq (p := n % 2 = 0))) (even_impl n)

/-- Even が決定可能であることを示す -/
instance (n : Nat) : Decidable (Even n) :=
  decidable_of_bool_iff (Even n) (evenComp n) (evenComp_spec n)

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

/- ## 排中律と決定可能性

命題 `P : Prop` が決定可能というのは、実際のところ「`P` の証明または `¬ P` の証明を持っている」ということを意味します。したがって、`P` の証明または `¬ P` の証明のいずれかが手に入っているのであれば、そこから `Decidable P` のインスタンスを構築することができ、`P` は決定可能であるといえます。
-/

instance {P : Prop} (h : P ⊕' (¬ P)) : Decidable P := by
  cases h with
  | inl h =>
    apply Decidable.isTrue
    exact h
  | inr h =>
    apply Decidable.isFalse
    exact h

/-
もっと言えば、排中律を利用してよければ任意の命題 `P : Prop` に対して `P` の証明または `¬ P` の証明を得ることができるので、すべての命題は決定可能になります。

これはもちろん、「どんな命題に対しても、それを決定できるアルゴリズムが作れる」という意味ではありません。逆です。`Decidable` 型クラスが意味を失ってしまうということです。
-/

/-- 排中律を利用すれば任意の命題について、肯定または否定の証明が手に入る -/
noncomputable example (P : Prop) : P ⊕' (¬ P) := by
  by_cases h : P
  case pos => exact PSum.inl h
  case neg => exact PSum.inr h

/-- 排中律を仮定すれば、任意の命題は決定可能 -/
noncomputable instance (P : Prop) : Decidable P := by
  exact Classical.propDecidable P

/- 実際、排中律を使って得られた `Decidable` インスタンスは計算的な解釈を持たないため、そうやって `Decidable` インスタンスを得ても `decide` タクティクで証明をすることはできません。
-/

/-- 奇数を表す述語 -/
def Odd (n : Nat) : Prop := ∃ m : Nat, n = 2 * m + 1

-- 排中律を利用して決定可能にしている
noncomputable instance (n : Nat) : Decidable (Odd n) := by
  classical
  infer_instance

example : Odd 3 := by
  -- decide で証明ができない
  fail_if_success decide

  exists 1
