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

/- ## DecidableEq と BEq

`DecidableEq α` は、`α` の任意の2つの値 `a b : α` について、命題 `a = b` が決定可能であることを表します。
一方で `BEq α` は、`a == b` という `Bool` 値の比較を提供する型クラスです。
公式リファレンスの説明どおり、`BEq` はそれだけでは `==` が反射的であることも、命題としての等号 `=` と一致することも要求しません。

参照:
* [Boolean Equality Tests](https://lean-lang.org/doc/reference/latest/Type-Classes/Basic-Classes/#boolean-equality-tests)
* [Floating-Point Numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/)
-/

#check (DecidableEq : Type → Type)
#check (BEq : Type → Type)

/- `==` は `BEq` のインスタンスによって使えるようになります。-/

#check ((· == ·) : Nat → Nat → Bool)

namespace DecidableEqVsBEq --#

/- `BEq` は、命題としての等号と一致しない比較にも使えます。たとえば「同じ `id` なら同じアカウントだとみなす」という比較を定義できます。-/

structure Account where
  id : Nat
  name : String
  deriving DecidableEq, Repr

instance : BEq Account where
  beq a b := a.id == b.id

def alice : Account := { id := 1, name := "Alice" }
def alicia : Account := { id := 1, name := "Alicia" }

-- id が同じなので `BEq` では等しい
#guard (alice == alicia)

-- しかし命題としての等号では等しくない
example : alice ≠ alicia := by decide

/- `==` と `=` が一致することを使いたいときは、`LawfulBEq` が必要です。上の `Account` の `BEq` は `alice == alicia` が真なのに `alice ≠ alicia` なので、`LawfulBEq` ではありません。-/

/-⋆-//--
error: failed to synthesize
  LawfulBEq Account

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in --#
#synth LawfulBEq Account

/- 構造体のすべてのフィールドを比較する通常の等号でよければ、`BEq` と `LawfulBEq` は `deriving` できます。-/

structure Point where
  x : Nat
  y : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

#synth BEq Point
#synth LawfulBEq Point

#guard ({ x := 2, y := 3 } : Point) == { x := 2, y := 3 }

example : ({ x := 2, y := 3 } : Point) = { x := 2, y := 3 } := by decide

end DecidableEqVsBEq --#

/- `Float` は `DecidableEq` と `BEq` の違いが重要になる例です。Lean の `Float` は IEEE 754 の浮動小数点数に対応しており、公式リファレンスでは、浮動小数点数の等号は Lean の論理内では決定可能ではないと説明されています。-/

#check (inferInstance : BEq Float)

/-⋆-//--
error: failed to synthesize
  DecidableEq Float

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in --#
#synth DecidableEq Float

/- しかし `Float` には実行時の比較としての `BEq` はあります。たとえば `0.0 / 0.0` は `NaN` になり、IEEE 754 の比較では `NaN` は自分自身と比較しても等しくありません。-/

#guard ((0.0 : Float) / 0.0).isNaN

-- 自分自身と比較しても false になる
#guard !(((0.0 : Float) / 0.0) == ((0.0 : Float) / 0.0))

-- 通常の数値の比較は true になる
#guard ((1.0 : Float) == 1.0)

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
