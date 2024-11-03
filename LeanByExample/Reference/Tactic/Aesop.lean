/-
# aesop

`aesop` は汎用的かつ強力な自動証明のためのタクティクです。

Automated Extensible Search for Obvious Proofs (自明な証明の拡張可能な自動探索)からその名があります。様々なタクティクやルールを使用しながら最良優先探索を行い、証明を自動で終わらせようとします。
-/
import Aesop -- `aesop` を使用するため
import Mathlib.Tactic.Says

-- 以下 `X` `Y` `Z`を集合とする
variable {X Y Z : Type}

/-- 関数の単射性 -/
def Function.Injective (f : X → Y) : Prop := ∀ ⦃a₁ a₂ : X⦄, f a₁ = f a₂ → a₁ = a₂

open Function

-- 合成 `g ∘ f` が単射なら、`f` も単射
example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  show ∀ ⦃a₁ a₂ : X⦄, f a₁ = f a₂ → a₁ = a₂

  -- `simp_all` では示せない
  fail_if_success simp_all

  -- 示すべきことがまだまだあるように見えるが、一発で証明が終わる
  aesop

/-
## aesop?

`aesop` が成功するとき、`aesop?` に置き換えるとゴールを達成するのにどんなタクティクを使用したか教えてくれます。
-/

example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  aesop? says
    intro a₁ a₂ a
    apply hgfinj
    simp_all only [comp_apply]

/- なお上記の例により、`aesop` が実行の過程で `simp_all` タクティクや `intro` タクティク等を使用することがわかります。
特に、`aesop` は `simp_all` の強化版であるということができます。
実際には `aesop` は `simp_all` よりずっと多くの機能を持ちますが、固有の機能については [`add_aesop_rules`](#{root}/Reference/Declarative/AddAesopRules.md) のページを参照してください。-/

/- ## カスタマイズ
`aesop` はユーザがカスタマイズ可能です。補題やタクティクを登録することで、証明可能な命題を増やすことができます。
-/

/-- 自然数 n が正の数であることを表す命題 -/
inductive Pos : Nat → Prop
  | succ n : Pos (n + 1)

example : Pos 1 := by
  -- ルールが登録されていないので、`aesop` で示すことはできない
  fail_if_success aesop

  -- 手動でコンストラクタを `apply` することで証明できる
  apply Pos.succ

-- `Pos` 関連のルールを `aesop` に憶えさせる
attribute [aesop safe constructors] Pos

-- `aesop` で証明できるようになった！
example : Pos 1 := by aesop

/- 上記の例のように `[aesop]` 属性によってルールを追加することもできますし、[`add_aesop_rules`](../Declarative/AddAesopRules.md) というコマンドでルールを追加することもできます。-/

example (n : Nat) (h : Pos n) : 0 < n := by
  -- ルールが足りないので、`aesop` で示すことはできない
  fail_if_success aesop

  -- 手動で `h : Pos n` を分解して証明する
  rcases h with ⟨h⟩
  simp

-- `Pos` 関連のルールを `aesop` に追加
add_aesop_rules safe [cases Pos]

-- `aesop` で証明できるようになった！
example (n : Nat) (h : Pos n) : 0 < n := by
  aesop

/-
カスタマイズ方法の詳細を知りたい方は[aesopのリポジトリ](https://github.com/leanprover-community/aesop)をご参照ください。また、内部のロジックの詳細については論文 [Aesop: White-Box Best-First Proof Search for Lean](https://dl.acm.org/doi/pdf/10.1145/3573105.3575671) で説明されています。
-/
