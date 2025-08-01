import Playground.MyList.Append

variable {α : Type}

/-- リストの長さを返す -/
def MyList.length (l : MyList α) : Nat :=
  match l with
  | ⟦⟧ => 0
  | _ ::: tail => 1 + length tail

attribute [grind] MyList.length

@[simp, grind]
theorem MyList.length_nil (l : MyList α) : l.length = 0 ↔ l = ⟦⟧ := by
  constructor <;> intro h
  · cases l <;> grind
  · grind

namespace MyList

@[grind]
theorem append_length (l₁ l₂ : MyList α) :
    (l₁ ++ l₂).length = l₁.length + l₂.length := by
  induction l₁ with grind

end MyList
