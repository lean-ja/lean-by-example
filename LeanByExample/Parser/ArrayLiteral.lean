/- # 配列リテラル

`#[x₁, x₂, .. , xₙ]` は、[Array α](#{root}/Type/Array.md) の項を簡単に作るための構文です。
-/

/-⋆-//-- info: #[1, 2, 3] : Array Nat -/
#guard_msgs in --#
#check #[1, 2, 3]

/- もしこの構文がなければ、`Array α` の項を作るにはコンストラクタを利用するしかないので、次のように書く必要があります。 -/

/-- 標準の Array をまねて自作した配列型 -/
structure MyArray (α : Type) where
  toList : List α

abbrev List.toMyArray {α : Type} (xs : List α) : MyArray α := ⟨xs⟩

/-⋆-//-- info: [1, 2, 3].toMyArray : MyArray Nat -/
#guard_msgs in --#
#check List.toMyArray [1, 2, 3]

/- しかし、配列リテラル構文があるおかげで、次のように見やすく簡潔に書くことができます。 -/

syntax "my#[" term,*,? "]" : term

macro_rules
  | `(my#[ $elems,* ]) => `(List.toMyArray [ $elems,* ])

-- 項を作るのが楽になった！
#check (my#[1, 2, 3] : MyArray Nat)
