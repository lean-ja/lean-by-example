/- # Cantor-Bernstein の定理

本稿では以下の定理を証明します。

> **定理**: Cantor-Bernstein の定理
>
> 単射 `f : A → B` と単射 `g : B → A` があるとする。
> このとき全単射 `h : A → B` が存在する。

## 補題: 冪集合上の単調関数の不動点定理

補題として次の定理を使用するので証明します。

> **定理**: 冪集合上の単調関数の不動点定理
>
> `X` を集合とし、`Φ : Set X → Set X` を冪集合上の単調写像とする。
> つまり任意の集合 `A, B : Set X` に対して `A ⊆ B → Φ A ⊆ Φ B` が成り立つとする。
> このとき、`Φ U = U` となる集合 `U : Set X` が存在する。
-/

/-
### 証明

以下のように、具体的に不動点となる部分集合 `U : Set X` を構成することができます。
-/
import Mathlib.Data.Set.Lattice.Bounded

variable {X : Type} (Φ : Set X → Set X)

-- Φ は単調
variable (hmono : ∀ A B : Set X, A ⊆ B → Φ A ⊆ Φ B)

-- そのままだと仮定(定理の引数)に含まれないので include する
include hmono in

theorem power_fixpoint : ∃ U : Set X, Φ U = U := by
  -- 集合族 𝒟 を以下のように定義する。
  let 𝒟 := { S : Set X | S ⊆ Φ S }

  -- 𝒟 の上限を取って、それを U とする。
  let U : Set X := ⋃ S ∈ 𝒟, S

  -- U の定義により、𝒟 に対する上界になっている。
  -- つまり ∀ S ∈ 𝒟, S ⊆ U
  have u_upper : ∀ S ∈ 𝒟, S ⊆ U := by
    intro (S : Set X) (hS : S ∈ 𝒟)
    exact Set.subset_biUnion_of_mem (u := id) hS

  -- このとき U ∈ 𝒟 を証明できる。
  have u_mem_d : U ∈ 𝒟 := by
    -- 𝒟 の定義により U ⊆ Φ U を示せばよい。
    suffices U ⊆ Φ U from by
      assumption

    -- それには、任意に S ∈ 𝒟 が与えられたとして、
    -- S ⊆ Φ U を示せば十分。
    suffices ∀ S ∈ 𝒟, S ⊆ Φ U from by
      aesop

    -- そこで S ∈ 𝒟 が与えられたとする。
    intro (S : Set X) (hS : S ∈ 𝒟)

    -- すると以下のように示せる。
    have : S ⊆ Φ U := calc
      _ ⊆ Φ S := hS -- 𝒟 の定義より
      _ ⊆ Φ U := by grind only -- S ⊆ U と Φ の単調性から
    assumption

  -- U ∈ 𝒟 ということは、言い換えると U ⊆ Φ U である。
  have u_mem_d' : U ⊆ Φ U := by grind

  -- Φ の単調性から、Φ U ⊆ Φ (Φ U) が成り立つ。
  have : Φ U ⊆ Φ (Φ U) := by grind

  -- これはつまり、Φ U ∈ 𝒟 を意味する。
  have : Φ U ∈ 𝒟 := by grind

  -- U は 𝒟 の上界だったから、
  -- Φ U ⊆ U が成り立つ。
  have : Φ U ⊆ U := by grind

  -- したがって両方向の包含関係が示せたので、
  -- Φ U = U である。
  grind only

/- ### 証明のアイデア

上記の証明において集合族 `𝒟 := { S : Set X | S ⊆ Φ S }` を考えてその上限 `U := ⋃ S ∈ 𝒟, S` を定義するのがキモでしたが、これはどのようにすれば思いつくのでしょうか？

これは次のように図を描いてみるとわかりやすくなります。

![不動点の図](./PowerFixPoint/fixed_point.svg)

ここで横軸と縦軸は、ともに `Set X` を表しています。
`Set X` は実数全体のように線形順序ではありませんが、順序関係自体は入っているので無理やり直線で表しています。
このように図で示してみると、`𝒟` というのは「不動点 `U` より小さい部分全体」であるというのがわかります。
-/

/- ### もう一つの証明

証明のアイデアを説明する図を見ていると、新たなアイデアが湧きます。
「不動点より小さい部分」に着目するのではなくて、「不動点より大きい部分」に着目したらどうなるでしょうか？
実は、そのようにしても証明が双対になるだけで、問題なく証明ができます。
-/

recall power_fixpoint {X : Type} (Φ : Set X → Set X)
  (hmono : ∀ (A B : Set X), A ⊆ B → Φ A ⊆ Φ B)
    : ∃ U, Φ U = U := by
  -- 「不動点より大きい部分全体」を考えてそれを集合族 ℰ とする。
  let ℰ := { S : Set X | Φ S ⊆ S }

  -- ℰ の下限をとって、それを V とする。
  let V : Set X := ⋂ S ∈ ℰ, S

  -- V の定義により、V は ℰ に対する下界になっている。
  -- つまり ∀ S ∈ ℰ, V ⊆ S
  have v_lower : ∀ S ∈ ℰ, V ⊆ S := by
    intro (S : Set X) (hS : S ∈ ℰ)
    exact Set.iInter₂_subset_of_subset (Φ S) (hmono (Φ S) S hS) hS

  -- このとき V ∈ ℰ を証明できる。
  have v_mem_e : V ∈ ℰ := by
    -- ℰ の定義により、Φ V ⊆ V を示せばよい
    suffices Φ V ⊆ V from by
      assumption

    -- それには、任意に S ∈ 𝒟 が与えられたとして
    -- Φ V ⊆ S を示せばよい
    suffices ∀ S ∈ ℰ, Φ V ⊆ S from by
      aesop

    -- そこで S ∈ ℰ が与えられたとする。
    intro (S : Set X) (hS : S ∈ ℰ)

    -- すると以下のように示せる。
    have : Φ V ⊆ S := calc
      _ ⊆ Φ S := by grind only
      _ ⊆ S := by grind only [usr Set.mem_ofPred_eq]
    assumption

  -- V ∈ ℰ ということは、言い換えると Φ V ⊆ V である。
  have v_mem_e' : Φ V ⊆ V := by grind

  -- Φ の単調性から、Φ (Φ V) ⊆ Φ V である。
  have : Φ (Φ V) ⊆ Φ V := by grind

  -- これはつまり、Φ V ∈ ℰ を意味する。
  have : Φ V ∈ ℰ := by grind

  -- V は ℰ の下界だったから、
  -- V ⊆ Φ V が成り立つ。
  have : V ⊆ Φ V := by grind

  -- したがって両方向の包含関係が示せたので、
  -- V = Φ V である。
  grind

/- ## 定理の証明

不動点定理を使って、メインの定理を証明します。
-/

variable {A B : Type}
variable (f : A → B) (g : B → A)

open Function in

theorem cantor_bernstein (injf : Injective f) (injg : Injective g) : ∃ h : A → B, Bijective h := by
  -- Φ という集合関数を次のように定義する
  let Φ : Set A → Set A := fun S => (g '' (f '' S)ᶜ)ᶜ

  -- このとき Φ は単調
  have hΦ : ∀ S T : Set A, S ⊆ T → Φ S ⊆ Φ T := by grind

  -- 不動点定理を適用して Φ U = U となる U を構成する。
  obtain ⟨U, hU⟩ := power_fixpoint Φ hΦ
  replace hU : Uᶜ = g '' (f '' U)ᶜ := by grind
  have houtside : ∀ a ∉ U, ∃ b, b ∉ f '' U ∧ g b = a := by
    exact fun a ha => (Set.ext_iff.mp hU a).mp ha

  -- U 上では f、それ以外では g の逆向きの対応を使って h を構成する。
  classical
  let h : A → B := fun a =>
    if ha : a ∈ U then f a else (houtside a ha).choose
  have h_on (a : A) (ha : a ∈ U) : h a = f a := by
    simp [h, ha]
  have h_off (a : A) (ha : a ∉ U) : h a ∉ f '' U ∧ g (h a) = a := by
    simpa [h, ha] using (houtside a ha).choose_spec

  refine ⟨h, ?_, ?_⟩
  · -- 単射性: U の内外の像は重ならず、それぞれの部分で単射になる。
    intro a₁ a₂ heq
    grind only [Injective, Set.mem_image]
  · -- 全射性: f '' U の内側は f で、外側は g の逆向きの対応で覆う。
    intro b
    by_cases hb : b ∈ f '' U
    · grind
    · have hgb : g b ∉ U := by
        exact (Set.ext_iff.mp hU (g b)).mpr ⟨b, hb, rfl⟩
      grind only
