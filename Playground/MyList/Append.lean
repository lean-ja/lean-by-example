import Playground.MyList.Basic

namespace MyList

variable {α : Type}

protected def append (l₁ l₂ : MyList α) : MyList α :=
  match l₁ with
  | m[] => l₂
  | head ::: tail => head ::: (MyList.append tail l₂)

/-- `MyList.append`を`++`で書けるようにする -/
instance : Append (MyList α) where
  append := MyList.append

#see List.cons_append
@[simp, grind _=_]
theorem cons_append (head : α) (tail l : MyList α) :
    head ::: tail ++ l = head ::: (tail ++ l) := by
  rfl

theorem append_cons (head : α) (tail l : MyList α) :
    l ++ head ::: tail = l ++ (head ::: tail) := by
  induction l with
  | nil => rfl
  | cons h t ih => rfl

#see List.nil_append
@[simp, grind]
theorem nil_append (l : MyList α) : m[] ++ l = l := by
  rfl

#see List.append_nil
@[simp, grind]
theorem append_nil (l : MyList α) : l ++ m[] = l := by
  induction l with simp_all

end MyList
