/- # ext

`ext` は，外延性(extensionality)を使うタクティクです．外延性とは，「同じものから作られているものは同じである」という主張のことです．たとえば

* 集合 `A, B ⊂ α` について `A = B` は `x ∈ A ↔ x ∈ B` と同じ
* 2つの写像 `f g : A → B` があるとき `f = g` は `∀ a ∈ A, f a = g a` と同じ

といったことを指します．

`@[ext]` で登録されたルールを使用するため，集合の等式 `A = B` を示すときは `Mathlib.Data.SetLike.Basic` も必要です. -/
import Aesop -- `aesop` タクティクを使うために必要
import Mathlib.Data.SetLike.Basic -- `ext` タクティクで集合の等号を展開するために必要

variable {α : Type}

-- `s` と `t` は `α` の部分集合
variable (s t : Set α)

example : s ∩ t = t ∩ s := by
  -- `x ∈ α` を取る．
  ext x

  -- ` x ∈ s ∩ t ↔ x ∈ t ∩ s` を証明すればよい
  show x ∈ s ∩ t ↔ x ∈ t ∩ s

  aesop
