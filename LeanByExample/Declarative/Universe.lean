/- # universe

`universe` は、宇宙レベルを表す変数を宣言するコマンドです。`universe u` と宣言すると、そのスコープ内で `u` を宇宙変数として使えるようになります。
-/

universe u

#check (Type u)

/-
ここで **宇宙(universe)** とは、項が再び型であるような型のことです。たとえば `Nat` や `Bool` は型ですが、Lean ではそのような型も項として扱われ、`Type` という型を持ちます。
-/

#check (Nat : Type)
#check (Bool : Type)

/- `Type` 自身も型ですが、`Type : Type` ではなく `Type : Type 1` です。`Type 1` の型は `Type 2` です。以下、`Type 2` の型は `Type 3` 等と無限に続きます。-/

#check (Type : Type 1)
#check (Type 1 : Type 2)
#check (Type 2 : Type 3)

/- 一般に `Type u` の型は `Type (u + 1)` になります。 -/

#check (Type u : Type (u + 1))
