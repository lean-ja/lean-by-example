
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

structure GameState where
  board : Array (Array Cell)

def GameState.empty : GameState :=
  { board := Array.replicate 3 #[.empty, .empty, .empty]}

/-- ユーザー入力を受け取る -/
def getUserInput : IO String := do
  IO.print "> "
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  return input.trimAscii.copy

structure Position where
  /-- 何行目かを表す。0 ≤ x ≤ 2 -/
  x : Nat
  /-- 何列目かを表す。0 ≤ y ≤ 2 -/
  y : Nat

def Position.flatten (pos : Position) : Nat :=
  pos.x * 3 + pos.y

def Position.build (pos : Nat) : Position :=
  { x := pos / 3, y := pos % 3 }

def parsePosition (input : String) : Option Position :=
  let num? := input.toNat?
  match num? with
  | none => none
  | some num =>
    if 0 ≤ num ∧ num ≤ 8 then
      some ⟨num / 3, num % 3⟩
    else
      none

def Cell.display (c : Cell) (pos : Position) : String :=
  match c with
  | .empty => toString pos.flatten
  | _ => toString c

def GameState.display (state : GameState) : IO Unit := do
  let board := state.board
  let mut pos : Nat := 0
  IO.println "+--+--+--+"
  for i in [0:3] do
    let row := board[i]!
    for j in [0:3] do
      let displayText := row[j]!.display (Position.build pos)
      IO.print s!"| {displayText}"

      pos := pos + 1

    IO.println "|"
    IO.println "+--+--+--+"

/-- ゲームの盤面の状態を更新する -/
def GameState.update (state : GameState) (pos : Position) (c : Cell) : GameState :=
  let oldRow := state.board[pos.x]!
  let newRow := oldRow.set! pos.y c
  let newBoard := state.board.set! pos.x newRow
  { board := newBoard }

def main : IO Unit := do
  let mut gameState := GameState.empty
  gameState.display

  let input ← getUserInput
  let some pos := parsePosition input |
    throw <| IO.userError "1から9の数字を入力してください"

  gameState := gameState.update pos Cell.x
  gameState.display
