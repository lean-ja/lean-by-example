import Playground.MyList.C01Basic

variable {α : Type}

/-- リストの長さを返す -/
def MyList.length (l : MyList α) : Nat :=
  match l with
  | ⟦⟧ => 0
  | _ ::: tail => 1 + length tail

attribute [grind] MyList.length

example (head : α) (tail : MyList α) : (head ::: tail).length > 0 := by
  -- `grind`一発で示すことができる
  grind
