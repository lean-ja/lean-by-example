/- # ext

`ext` は、外延性(extensionality)を使うタクティクです。外延性とは、「同じものから作られているものは同じである」という主張のことです。たとえば、「2つの関数 `f g : A → B` があるとき `∀ a : A, f a = g a` ならば `f = g`」というのは外延性の一種で、**関数外延性(functional extensionality)** と呼ばれます。-/
import Aesop -- `aesop` タクティクを使うために必要 --#

example {A B : Type} (f g : A → B) (h : ∀ a : A, f a = g a) : f = g := by
  -- `x : A` を取って外延性を使用する
  ext x

  -- ゴールが `f x = g x` に変わる
  guard_target =ₛ f x = g x

  apply h

/- ## カスタマイズ
特定の型の外延性を登録し、`ext` タクティクで使用できるようにするには、外延性を述べた命題に `[ext]` 属性を付与します。
-/

universe u

/-- `α` を全体集合とする集合の全体。別の言い方をすれば、`α` のベキ集合。
`α` の部分集合と、`α` 上の述語を同一視している。-/
def Set (α : Type u) := α → Prop

namespace Set

variable {α : Type u}

/-- `x : α` が `s : Set α` の要素であるという命題。-/
def Mem (s : Set α) (x : α) : Prop := s x

/-- 集合らしく `s x` を `x ∈ s` と書けるようにする -/
instance : Membership α (Set α) := ⟨Mem⟩

/-- 集合の外延性。同じ要素からなる集合は等しい -/
theorem ext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  -- 関数外延性を使う
  apply funext

  intro x
  rw [show a x ↔ b x from h x]

#guard_msgs (drop warning) in --#
example {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  -- 最初は使えない
  fail_if_success ext x
  sorry

-- `[ext]` 属性を付与
attribute [ext] Set.ext

example {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  -- ext タクティクが使えるようになった！
  ext x
  apply h

end Set

/- ## 構造体に対する [ext] 属性

`[ext]` 属性は[構造体](#{root}/Declarative/Structure.md)に対しても与えることができます。このとき、その構造体に対して自動的に `.ext` と `.ext_iff` の２つの定理が生成されます。
-/

variable {α : Type}

structure Point (α : Type) where
  x : α
  y : α

-- 最初は存在しない
#guard_msgs (drop warning) in --#
#check_failure Point.ext
#guard_msgs (drop warning) in --#
#check_failure Point.ext_iff

-- `Point` に `[ext]` 属性を与える
attribute [ext] Point

-- 自動生成された定理
-- 各フィールドの値が等しければ、2つの `Point` は等しいという主張
#check (Point.ext : ∀{x y : Point α}, x.x = y.x → x.y = y.y → x = y)

-- 自動生成された定理その２
-- 2つの `Point` の点が等しいことは、各フィールドの値が等しいことと同値
#check (Point.ext_iff : ∀{x y : Point α}, x = y ↔ x.x = y.x ∧ x.y = y.y)

/- これにより、構造体に対して `ext` タクティクが使用できるようになります。 -/

structure Foo where
  x : Nat
  y : Nat

#guard_msgs (drop warning) in --#
example (p q : Foo) (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  -- 最初は ext タクティクが使えない
  fail_if_success ext
  sorry

-- `Foo` に `[ext]` 属性を与える
attribute [ext] Foo

example (p q : Foo) (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  -- ext タクティクが使えるようになった！
  ext
  · exact hx
  · exact hy
