import Playground.MyList.Basic

variable {α : Type}

variable (r : α → α → Prop)
local infixl:50 " ≼ " => r

@[grind cases, grind]
inductive Sorted : MyList α → Prop where
  | nil : Sorted ⟦⟧
  | single (a : α) : Sorted ⟦a⟧
  | cons (a b : α) (tail : MyList α) (ih : Sorted (b ::: tail)) (h : a ≼ b) :
    Sorted (a ::: b ::: tail)

@[simp]
theorem sorted_of_singleton {a : α} : Sorted r ⟦a⟧ := by grind
