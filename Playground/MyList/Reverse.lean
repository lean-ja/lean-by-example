import Playground.MyList.Append

namespace MyList

variable {α : Type}

/-- リストの順序を逆にする -/
def reverse (l : MyList α) : MyList α :=
  match l with
  | m[] => m[]
  | head ::: tail => reverse tail ++ head ::: m[]

#check m[1, 2, 3].reverse

end MyList
