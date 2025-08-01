import Playground.MyList.Append

namespace MyList

variable {α : Type}

/-- リストの順序を逆にする -/
@[grind]
def reverse (l : MyList α) : MyList α :=
  match l with
  | ⟦⟧ => ⟦⟧
  | head ::: tail => reverse tail ++ ⟦head⟧

@[grind _=_]
theorem reverse_append (l₁ l₂ : MyList α) :
  reverse (l₁ ++ l₂) = reverse l₂ ++ reverse l₁ := by
  -- `try?`で解くことができた。
  fun_induction reverse l₁ <;> grind

@[grind =, simp]
theorem reverse_reverse (l : MyList α) : reverse (reverse l) = l := by
  fun_induction reverse <;> grind

end MyList
