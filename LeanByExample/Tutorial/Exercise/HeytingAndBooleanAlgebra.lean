/- # Heyting 代数と Bool 代数
直観主義論理において、排中律 `P ∨ ¬ P` は独立な命題であることが知られています。つまり、証明も反証(否定を証明すること)もできません。今回の演習問題では、それに関連した話題として、Bool 代数ではない Heyting 代数が存在することを示します。

ここでは Mathlib をなぞるように理論を構成していきます。

## 半順序集合
まず準備として、半順序集合を定義します。半順序集合には順序が定義されていますが、要素を2つ与えられたときにどちらが大きいのか比較できるとは限らないことに注意してください。
-/
import Aesop --#
set_option autoImplicit false --#
set_option relaxedAutoImplicit false --#

/-- 半順序集合 -/
class PartialOrder (α : Type) extends LE α, LT α where
  /-- `≤` は反射的である -/
  le_refl : ∀ a : α, a ≤ a

  /-- `≤` は推移的である -/
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c

  /-- `<` のデフォルト実装 -/
  lt := fun a b => a ≤ b ∧ ¬ b ≤ a

  /-- `<` と `≤` の関係 -/
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a

  /-- `≤` は半対称的 -/
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

/- ## 束
半順序集合であって、任意の2つの要素 `a, b` に対して上限 `a ⊔ b` と下限 `a ⊓ b` が存在するものを束といいます。上限は最小の上界を意味し、下限は最大の下界を意味します。

上限の記号 `⊔` は論理和 `∨` に、下限の記号 `⊓` は論理積 `∧` に、それぞれ似ています。またそれぞれ集合の合併 `∪` と共通部分 `∩` にも似ています。これは、`Prop` と `Set α` がともに束になっていることと整合性があります。
-/

section Lattice

/-- `⊔` という記号のための型クラス -/
class Sup (α : Type) where
  /-- 最小上界、上限 -/
  sup : α → α → α

/-- `⊓` という記号のための型クラス -/
class Inf (α : Type) where
  /-- 最大下界、下限 -/
  inf : α → α → α

@[inherit_doc] infixl:68 " ⊔ " => Sup.sup

@[inherit_doc] infixl:69 " ⊓ " => Inf.inf

/-- 任意の2つの要素 `a, b` に対して上限 `a ⊔ b` が存在するような半順序集合 -/
class SemilatticeSup (α : Type) extends Sup α, PartialOrder α where
  /-- `a ⊔ b` は `a` と `b` の上界になっている -/
  le_sup_left : ∀ a b : α, a ≤ a ⊔ b

  /-- `a ⊔ b` は `a` と `b` の上界になっている -/
  le_sup_right : ∀ a b : α, b ≤ a ⊔ b

  /-- `a ⊔ b` は `a`, `b` の上界の中で最小のもの -/
  sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c

/--  任意の2つの要素 `a, b` に対して下限 `a ⊓ b` が存在するような半順序集合 -/
class Semilatticeinf (α : Type) extends Inf α, PartialOrder α where
  /-- `a ⊓ b` は `a` と `b` の下界になっている -/
  inf_le_left : ∀ a b : α, a ⊓ b ≤ a

  /-- `a ⊓ b` は `a` と `b` の下界になっている -/
  inf_le_right : ∀ a b : α, a ⊓ b ≤ b

  /-- `a ⊓ b` は `a`, `b` の下界の中で最大のもの -/
  le_inf : ∀ a b c : α, c ≤ a → c ≤ b → c ≤ a ⊓ b

set_option structureDiamondWarning false in --#
/-- 束 -/
class Lattice (α : Type) extends SemilatticeSup α, Semilatticeinf α

end Lattice

/- ## Heyting 代数
ここまでの準備の下、Heyting 代数を定義することができます。Heyting 代数とは束であって、以下の条件を満たすものです。

1. 最大の要素 `⊤` が存在する。
2. 最小の要素 `⊥` が存在する。
3. 下限 `· ⊓ b` の右随伴 `b ⇨ ·` が存在する。つまり任意の `a, b, c` に対して `a ⊓ b ≤ c` と `a ≤ b ⇨ c` が同値。
-/

section HeytingAlgebra

/-- `⊤` という記号のための型クラス -/
class Top (α : Type) where
  /-- 最大元 -/
  top : α

@[inherit_doc] notation "⊤" => Top.top

/-- `⊥` という記号のための型クラス -/
class Bot (α : Type) where
  /-- 最小元 -/
  bot : α

@[inherit_doc] notation "⊥" => Bot.bot

/-- `⇨` という記号のための型クラス -/
class HImp (α : Type) where
  /-- Heyting 含意 `⇨` -/
  himp : α → α → α

@[inherit_doc] infixr:60 " ⇨ " => HImp.himp

/-- `ᶜ` という記号のためのクラス -/
class HasCompl (α : Type) where
  /-- 補元 -/
  compl : α → α

@[inherit_doc] postfix:1024 "ᶜ" => HasCompl.compl

/-- Heyting 代数 -/
class HeytingAlgebra (α : Type) extends Lattice α, Top α, Bot α, HasCompl α, HImp α where
  /-- ⊤ は最大元 -/
  le_top : ∀ a : α, a ≤ ⊤

  /-- ⊥ は最小元 -/
  bot_le : ∀ a : α, ⊥ ≤ a

  /-- `· ⊓ b` の右随伴 `b ⇨ ·` が存在する -/
  le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c

  /-- 補元の定義 -/
  himp_bot (a : α) : a ⇨ ⊥ = aᶜ

end HeytingAlgebra

/- ## 問1 Prop は Heyting 代数

いよいよ問題です。`Prop` が Heyting 代数のインスタンスであることを示しましょう。

しかし、今回は証明の `sorry` の部分を埋めていただくという問題ではありません。逆に、こちらで用意した証明が通るようにしていただくのが問題です。

こちらで用意した証明は、すべて `aesop` という単一のタクティクで完結しています。`aesop` は補題やタクティクを登録することにより、ユーザがカスタマイズ可能なタクティクですので、うまくカスタマイズして用意された証明が通るようにしてください。[`add_aesop_rules`](#{root}/Reference/Declarative/AddAesopRules.md) の記事が参考になると思います。

### 問1.1 半順序集合であること
-/
section PropInstance --#

/-- `P Q : Prop` に対して、順序関係 `P ≤ Q` を
`P → Q` が成り立つこととして定める -/
instance : LE Prop where
  le a b := a → b

/-- `P < Q` の定義は `P → Q` かつ同値ではないこと -/
instance : LT Prop where
  lt a b := (a → b) ∧ ¬ (b → a)

-- ここに `local add_aesop_rules` コマンドを追加して証明が通るようにしてください。
-- いくつルールを追加しても構いません。
-- 以下に示すのは一例です:
local add_aesop_rules unsafe 50% tactic [(by apply True.intro)]

/-- 上記の定義のもとで `Prop` は半順序集合 -/
instance : PartialOrder Prop where
  le_refl := by aesop
  le_trans := by aesop
  lt_iff_le_not_le := by aesop
  le_antisymm := by aesop

/- ### 問1.2 束であること -/

/-- 論理和 `∨` を上限とする -/
instance : Sup Prop where
  sup a b := a ∨ b

/-- 論理積 `∧` を下限とする -/
instance : Inf Prop where
  inf a b := a ∧ b

-- ここに `local add_aesop_rules` コマンドを追加して証明が通るようにしてください。
-- いくつルールを追加しても構いません。
-- 以下に示すのは一例です:
local add_aesop_rules safe tactic [(by simp only [Nat.add_zero])]

/-- 上記の定義のもとで `Prop` は束 -/
instance : Lattice Prop where
  le_sup_left := by aesop
  le_sup_right := by aesop
  sup_le := by aesop
  inf_le_left := by aesop
  inf_le_right := by aesop
  le_inf := by aesop

/- ### 問1.3 Heyting 代数であること -/

/-- `a ⇨ b` には `a → b` を対応させる -/
instance : HImp Prop where
  himp a b := a → b

/-- `aᶜ` には `¬ a` を対応させる -/
instance : HasCompl Prop where
  compl a := ¬ a

/-- True が最大元 -/
instance : Top Prop where
  top := True

/-- False が最小元 -/
instance : Bot Prop where
  bot := False

-- ここに `local add_aesop_rules` コマンドを追加して証明が通るようにしてください。
-- いくつルールを追加しても構いません。
-- 以下に示すのは一例です:
local add_aesop_rules norm simp [Nat.add_zero]

instance : HeytingAlgebra Prop where
  le_top := by aesop
  bot_le := by aesop
  le_himp_iff := by aesop
  himp_bot := by aesop

end PropInstance --#
/- ## 問2 Bool 代数でない Heyting 代数
Bool 代数を定義し、Heyting 代数であって Bool 代数でない例を具体的に構成します。これにより、Heyting 代数の公理から Bool 代数の公理を証明することができないことが分かります。

反例の集合はシンプルで、３つの要素からなる集合として構成することができます。
-/
section BooleanCounterExample --#

/-- Bool 代数 -/
class BooleanAlgebra (α : Type) extends HeytingAlgebra α where
  /-- `x ⊓ xᶜ = ⊥` が成り立つ -/
  inf_compl_le_bot : ∀ x : α, x ⊓ xᶜ ≤ ⊥

  /-- `⊤ = x ⊔ xᶜ` が成り立つ -/
  top_le_sup_compl : ∀ x : α, ⊤ ≤ x ⊔ xᶜ

/-- `{0, 1, 2}` という集合。これが反例になる。 -/
abbrev Three := Fin 3

/- ### 問2.1 半順序集合であること -/

-- 順序関係が既に定義されている
#synth LE Three

-- ここに `local add_aesop_rules` コマンドを追加して証明が通るようにしてください。
-- いくつルールを追加しても構いません。

instance : PartialOrder Three where
  le_refl := by aesop
  le_trans := by aesop
  le_antisymm := by aesop
  lt_iff_le_not_le := by aesop

/- ### 問2.2 束であること -/

/-- 上限の定義 -/
instance : Sup Three where
  sup a b := {
    val := max a.val b.val
    isLt := by omega
  }

/-- 下限の定義 -/
instance : Inf Three where
  inf a b := {
    val := min a.val b.val
    isLt := by omega
  }

-- ここに `local add_aesop_rules` コマンドを追加して証明が通るようにしてください。
-- いくつルールを追加しても構いません。

/-- 束になる -/
instance : Lattice Three where
  le_sup_left := by aesop
  le_sup_right := by aesop
  sup_le := by aesop
  inf_le_left := by aesop
  inf_le_right := by aesop
  le_inf := by aesop

/- ### 問2.3 Heyting 代数であるが Bool 代数ではないこと -/

/-- 最大元は2 -/
instance : Top Three where
  top := 2

/-- 最小元は0 -/
instance : Bot Three where
  bot := 0

/-- Heyting 含意の定義 -/
instance : HImp Three where
  himp a b := {
    val := if a ≤ b then 2 else b.val
    isLt := by aesop
  }

/-- 補元の定義 -/
instance : HasCompl Three where
  compl a := {
    val := if a = 0 then 2 else 0
    isLt := by aesop
  }

-- ここに `local add_aesop_rules` コマンドを追加して証明が通るようにしてください。
-- いくつルールを追加しても構いません。

/-- Heyting 代数になる -/
instance : HeytingAlgebra Three where
  le_top := by aesop
  bot_le := by aesop
  le_himp_iff := by aesop
  himp_bot := by aesop

/-- Three は上記の構成の下で Bool 代数ではない -/
theorem three_not_boolean : (1 : Three) ⊔ 1ᶜ ≠ ⊤ := by aesop

end BooleanCounterExample --#
