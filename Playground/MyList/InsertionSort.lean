import Playground.MyList.C02Append

variable {α : Type} {β : Type} (r : α → α → Prop) (s : β → β → Prop)
variable [DecidableRel r] [DecidableRel s]

local infixl:50 " ≼ " => r
local infixl:50 " ≼ " => s

/-! ### Insertion sort -/


section InsertionSort

/-- `orderedInsert a l` inserts `a` into `l` at such that
  `orderedInsert a l` is sorted if `l` is. -/
@[simp]
def orderedInsert (a : α) : MyList α → MyList α
  | ⟦⟧ => ⟦a⟧
  | b ::: l =>
    if a ≼ b then
      a ::: b ::: l
    else
      b ::: orderedInsert a l

theorem orderedInsert_of_le {a b : α} (l : MyList α) (h : a ≼ b) :
    orderedInsert r a (b ::: l) = a ::: b ::: l := by
  grind [orderedInsert]

/-- `insertionSort l` returns `l` sorted using the insertion sort algorithm. -/
@[simp]
def insertionSort : MyList α → MyList α
  | ⟦⟧ => ⟦⟧
  | b ::: l => orderedInsert r b (insertionSort l)

