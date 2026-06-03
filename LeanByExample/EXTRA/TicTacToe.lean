
inductive Cell where
  | empty
  | x
  | o
deriving Inhabited

protected def Cell.toString (c : Cell) : String :=
  match c with
  | empty => " "
  | x => "×"
  | o => "○"

instance : ToString Cell where
  toString := Cell.toString

def Cell.display (c : Cell) (position : Nat) : String :=
  match c with
  | .empty => toString position
  | _ => toString c

structure GameState where
  board : Array (Array Cell)

def GameState.empty : GameState :=
  { board := Array.replicate 3 #[.empty, .empty, .empty]}

def GameState.display (state : GameState) : IO Unit := do
  let board := state.board
  let mut position := 1
  IO.println "+--+--+--+"
  for i in [0:3] do
    let row := board[i]!
    for j in [0:3] do
      let displayText := row[j]!.display position
      IO.print s!"| {displayText}"

      position := position + 1
    IO.println "|"
    IO.println "+--+--+--+"

/-- ユーザー入力を受け取る -/
def getUserInput : IO String := do
  IO.print "> "
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  return input.trimAscii.copy

def main : IO Unit := do
  let mut gameState := GameState.empty
  gameState.display
