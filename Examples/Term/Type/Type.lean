/- # Type
`Type` は、型全体がなす型宇宙です。ここで型宇宙とは、項が再び型であるような型のことをいいます。

たとえば `Nat` や `Int`, `Bool` や `String` などが `Type` の項になっています。
-/
import Mathlib.Tactic --#

#check (Nat : Type)
#check (Int : Type)
#check (Bool : Type)
#check (String : Type)

/- ## 可算無限個の宇宙
では `Type` 自身の型はどうなっているのでしょうか？`Type` は明らかに型なので `Type : Type` となっているのでしょうか。実際に試してみると、`Type` の型は `Type 1` です。
-/

#check (Type : Type 1)

/- そして `Type 1` の型は `Type 2` であり、また `Type 2` の型は `Type 3` であり…と無限に続いていきます。 -/

#check (Type 1 : Type 2)
#check (Type 2 : Type 3)

universe u
#check (Type u : Type (u+1))

/- `Type` は実は `Type 0` の略記になっています。 -/

example : Type = Type 0 := rfl

/- また、`Prop` と `Type u` という２つの宇宙の系列をまとめて書き表すために `Sort u` という書き方があります。 `Prop = Sort 0` で、以降順に宇宙レベルが上がっていきます。-/

example : Sort 0 = Prop := rfl
example : Sort 1 = Type 0 := rfl
example : Sort 2 = Type 1 := rfl
example : Sort (u + 1) = Type u := rfl

/- ## なぜ Type : Type ではないのか
何故このような仕様になっているのでしょうか。可算無限個の宇宙を用意するよりも `Type : Type` とした方が簡単ではないでしょうか？実は、`Type : Type` となるような型理論を採用すると矛盾が生じてしまいます。

これは **Girard のパラドックス** と呼ばれる有名な結果です。しかし Girard のパラドックスを直接説明しようとすると準備が多く必要になるので、ここでは Girard のオリジナルの議論を追うことはせず、代わりに濃度による簡潔な議論を紹介します。

以下証明を説明します。仮に `Type` が `Type` の項だったとしましょう。このとき `α := Type` とすることにより、ある `Type` の項 `α` を選べば、全射 `f : α → Type` を作れることがわかります。したがって、任意の型 `α : Type` に対して関数 `f : α → Type` が全射になることはありえないことを示せばよいことになります。

補題として Cantor の定理の単射バージョンが必要なのでここで示します。
-/

open Function

/-- Cantor の定理の単射バージョン。
ベキ集合からの関数は、単射ではありえない。 -/
theorem my_cantor_injective {α : Type} (f : Set α → α) : ¬ Injective f := by
  -- f が単射だと仮定する
  intro h

  -- X : Set α を次のように定義する
  let X : Set α := { y | ∃ C : Set α, y = f C ∧ f C ∉ C }

  -- このとき f X ∈ X であるかどうかを考える

  -- f X ∈ X だと仮定すると矛盾が導かれる
  have lem : f X ∈ X → False := by
    intro hX

    -- X の定義から、ある C : Set α が存在して
    -- f X = f C かつ f C ∉ C が成り立つ
    have ⟨C, hfC, hC⟩ := hX

    -- f は単射なので X = C
    have hXC : X = C := h hfC

    -- よって f X ∉ X となり矛盾
    rw [← hXC] at hC
    contradiction

  -- したがって f X ∉ X である
  -- ところが X の定義から、これはまさに f X ∈ X であることを意味する
  have : f X ∈ X := ⟨X, rfl, lem⟩

  -- これは矛盾
  contradiction

/- この補題に帰着することにより、小さい型から型宇宙への全射がないことを示せます。-/

theorem not_surjective_Type {α : Type} (f : α → Type) : ¬ Surjective f := by
  -- f が全射だと仮定する
  intro h

  -- f から依存和型を構成する
  let T : Type := (a : α) × f a

  -- f は全射なので、Set T の逆像の要素が存在する
  let ⟨x, hx⟩ := h (Set T)

  -- 関数 `g : Set T → T` を構成できる
  let g : Set T → T := fun s ↦ ⟨x, cast hx.symm s⟩

  -- このとき、g は単射になる
  have hg : Injective g := by
    intros s t h
    dsimp [g] at h
    apply_fun Sigma.snd at h
    simpa using h

  -- これはカントールの定理に反する
  exact my_cantor_injective g hg
