/- # ∀

`∀` 記号は基本的に、全称量化を表します。つまり述語 `P : α → Prop` に対して、`∀ x : α, P x` は「すべての `x : α` に対して `P x` が成り立つ」という意味になります。

しかし、`∀` は述語以外のものに対しても実は使うことができます。
-/

#check ∀ n : Nat, Vector Nat n

/- この場合何を意味するかというと、`∀ a : A, B` は `(a : A) → B` と同じ意味になります。-/

set_option pp.foralls false

/-⋆-//-- info: (n : Nat) → Vector Nat n : Type -/
#guard_msgs in --#
#check ∀ n : Nat, Vector Nat n

/- 実際のところ両者は常に同じです。型が `Prop` になるときは、カリー・ハワード同型対応により「命題は型、証明はその項」なので全称量化の意味になるというだけで、型としては同じものです。型が `Prop` になるときだけ、見やすいので `∀` 記号を使う慣習になっています。 -/

universe u

variable {A : Type} {B : A → Sort u}

example : ((a : A) → B a) = (∀ a : A, B a) := by rfl
