/- # 冪集合上での不動点定理

本項では以下の定理を証明します。

> **定理**: 冪集合上の不動点定理
>
> `X` を集合とし、`Φ : Set X → Set X` を冪集合上の単調写像とする。
> つまり任意の集合 `A, B : Set X` に対して `A ⊆ B → Φ A ⊆ Φ B` が成り立つとする。
> このとき、`Φ U = U` となる集合 `U : Set X` が存在する。
-/

/-
## 定理の証明

以下のように、具体的に不動点となる部分集合 `U : Set X` を構成することができます。
-/
import Mathlib.Data.Set.Lattice.Bounded

variable {X : Type} (Φ : Set X → Set X)

-- Φ は単調
variable (hmono : ∀ A B : Set X, A ⊆ B → Φ A ⊆ Φ B)

-- そのままだと仮定(定理の引数)に含まれないので include する
include hmono

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
