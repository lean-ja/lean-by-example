/- # Type
`Type` は、型がなす型宇宙です。ここで型宇宙とは、項が再び型であるような型のことをいいます。

たとえば [`Nat`](#{root}/Type/Nat.md) や `Int`, `Bool` や `String` などが `Type` の項になっています。
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

これは **ジラールのパラドックス(Girard's paradox)** と呼ばれる有名な結果です。しかしジラールのパラドックスを直接説明しようとすると準備が多く必要になるので、ここではジラールのオリジナルの議論を追うことはせず、代わりに濃度による簡潔な議論を紹介します。

以下証明を説明します。仮に `Type` が `Type` の項だったとしましょう。このとき `α := Type` とすることにより、ある `Type` の項 `α` を選べば、全射 `f : α → Type` を作れることがわかります。したがって、任意の型 `α : Type` に対して関数 `f : α → Type` が全射になることはありえないことを示せばよいことになります。

これは **カントールの定理(Cantor's theorem)** の単射バージョンに帰着して示すことができます。
-/

open Function

theorem not_surjective_Type {α : Type} (f : α → Type) : ¬ Surjective f := by
  -- f が全射だと仮定する
  intro h

  -- f から依存ペア型を構成する
  let T : Type := (a : α) × f a

  -- f は全射なので、Set T の逆像の要素が存在する
  let ⟨x, hx⟩ := h (Set T)

  -- 関数 `g : Set T → T` を構成できる
  let g : Set T → T := fun s ↦ ⟨x, cast hx.symm s⟩

  -- このとき、g は単射になる
  have hg : Injective g := by
    intro s t h
    grind

  -- これはカントールの定理に反する
  exact cantor_injective g hg
