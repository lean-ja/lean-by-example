variable {α : Type}

/-- 二項関係 `R` がリストの隣接要素に対して成立するという述語。 -/
inductive IsChain (R : α → α → Prop) : List α → Prop
  | nil : IsChain R []
  | single (a : α) : IsChain R [a]
  | cons_cons {a b : α} {l : List α} (hab : R a b) (hchain : IsChain R (b :: l)) :
    IsChain R (a :: b :: l)

attribute [grind cases] IsChain
attribute [simp] IsChain.nil IsChain.single
attribute [grind <=] IsChain.cons_cons IsChain.single IsChain.nil

variable {R : α → α → Prop}

/-- リストの最後の要素を取得する。 -/
@[simp]
def last? (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [a] => some a
  | _ :: b :: bs => last? (b :: bs)

theorem last?_cons_exists (xs : List α) (x : α) :
    ∃ y : α, some y = last? (x :: xs) := by
  induction xs generalizing x with simp_all

-- `[grind]` 属性は、登録すべきパターンを見つけられない。
/-⋆-//--
error: invalid `grind` theorem, failed to find an usable pattern using different modifiers
-/
#guard_msgs in --#
attribute [grind] last?_cons_exists

-- `grind_pattern` コマンドなら、`last? (x :: xs)` を見たときに
-- `last?_cons_exists` を使うよう明示的に指定できる。
grind_pattern last?_cons_exists => last? (x :: xs)

@[grind =]
theorem IsChain.append {xs ys : List α} :
    IsChain R (xs ++ ys) ↔
      match last? xs, ys with
      | none, _ => IsChain R ys
      | _, [] => IsChain R xs
      | some x, b :: _ => IsChain R xs ∧ R x b ∧ IsChain R ys := by
  fun_induction last? xs with grind
