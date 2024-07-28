/- # ext

`ext` は、外延性(extensionality)を使うタクティクです。外延性とは、「同じものから作られているものは同じである」という主張のことです。たとえば

* 集合 `A, B ⊂ α` について `A = B` は `x ∈ A ↔ x ∈ B` と同じ
* 2つの写像 `f g : A → B` があるとき `f = g` は `∀ a ∈ A, f a = g a` と同じ

といったことを指します。

`@[ext]` で登録されたルールを使用するため、集合の等式 `A = B` を示すときは `Mathlib.Data.SetLike.Basic` も必要です。-/
import Aesop -- `aesop` タクティクを使うために必要
import Mathlib.Data.SetLike.Basic -- `ext` タクティクで集合の等号を展開するために必要
namespace Ext --#

variable {α : Type}

-- `s` と `t` は `α` の部分集合
variable (s t : Set α)

example : s ∩ t = t ∩ s := by
  -- `x ∈ α` を取る。
  ext x

  -- ` x ∈ s ∩ t ↔ x ∈ t ∩ s` を証明すればよい
  show x ∈ s ∩ t ↔ x ∈ t ∩ s

  aesop

/- ## ext 属性
`ext` 属性を命題に与えると、上記のようにその命題は `ext` タクティクで利用できるようになります。さらに、`ext` 属性は構造体に対しても与えることができます。このとき、その構造体に対して自動的に `.ext` と `.ext_iff` の２つの定理が生成されます。
-/

variable {α : Type}

structure Point (α : Type) where
  x : α
  y : α

-- 最初は存在しない
#check_failure Point.ext
#check_failure Point.ext_iff

-- `Point` に `ext` 属性を与える
attribute [ext] Point

-- 自動生成された定理
-- 各フィールドの値が等しければ、2つの `Point` は等しいという主張
#check (Point.ext : (x y : Point α) → x.x = y.x → x.y = y.y → x = y)

-- 自動生成された定理その２
-- 2つの `Point` の点が等しいことは、各フィールドの値が等しいことと同値
#check (Point.ext_iff : (x y : Point α) → x = y ↔ x.x = y.x ∧ x.y = y.y)

end Ext --#
