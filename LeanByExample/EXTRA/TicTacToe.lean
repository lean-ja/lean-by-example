
inductive Cell where
  | empty
  | x
  | o
deriving Inhabited, BEq

protected def Cell.toString (c : Cell) : String :=
  match c with
  | empty => " "
  | x => "×"
  | o => "○"

instance : ToString Cell where
  toString := Cell.toString

structure GameState where
  board : Vector (Vector Cell 3) 3

def GameState.empty : GameState :=
  let row := #v[Cell.empty, Cell.empty, Cell.empty]
  let board := #v[row, row, row]
  { board := board }

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
deriving DecidableEq, Inhabited

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

def grayText (s : String) : String :=
  s!"\x1b[90m{s}\x1b[0m"

def Cell.display (c : Cell) (pos : Position) : String :=
  match c with
  | .empty => grayText <| toString pos.flatten
  | _ => toString c

/-- ゲームの盤面の状態を表示する -/
def GameState.display (state : GameState) (indentSize : Nat := 5) : IO Unit := do
  let indent := " ".pushn ' ' indentSize
  let board := state.board
  let mut pos : Nat := 0
  IO.println s!"{indent}+--+--+--+"
  for hi : i in [0:3] do
    let row := board[i]
    IO.print indent
    for hj : j in [0:3] do
      let displayText := row[j].display (Position.build pos)
      IO.print s!"| {displayText}"

      pos := pos + 1

    IO.println s!"|"
    IO.println s!"{indent}+--+--+--+"

/-- 未着手のセルを列挙する -/
def GameState.unused (state : GameState) : Array Position :=
  let flatBoard := state.board.flatten
  let unusedIdxes := flatBoard.zipIdx
    |>.toArray
    |>.filter (fun (cell, _idx) => cell == .empty)
    |>.map (fun (_cell, idx) => idx)
  unusedIdxes.map Position.build

/-- その場所に着手できるかどうか判定する。既に着手済みなら着手できない。 -/
def GameState.allow (state : GameState) (pos : Position) : Bool :=
  if pos ∈ state.unused then
    true
  else
    false

/-- ゲームの盤面の状態を更新する。
注意: 既に着手済みの場所に置こうとしても何も起こらない -/
def GameState.update (state : GameState) (pos : Position) (c : Cell) : GameState :=
  let oldRow := state.board[pos.x]!
  let newRow := oldRow.set! pos.y c
  let newBoard := state.board.set! pos.x newRow
  { board := newBoard }

def Array.getRandom {α : Type} [Inhabited α] (xs : Array α) : IO α := do
  let idx ← IO.rand 0 (xs.size - 1)
  return xs[idx]!

/-- 未着手の場所をランダムに選ぶ -/
def getRandomPos (state : GameState) : IO Position := do
  let unused := state.unused
  let pos ← unused.getRandom
  return pos

inductive Result where
  /-- 進行中 -/
  | progress
  /-- x を持っているプレイヤーの勝ち -/
  | xwin
  /-- o を持っているプレイヤーの勝ち -/
  | owin
  /-- 引き分け -/
  | draw
deriving BEq

/-- `Cell` に対する述語 `P` が、どれかの行に対して成立する -/
def GameState.checkForRows (state : GameState) (P : Cell → Bool) : Bool :=
  let board := state.board
  (P board[0][0] && P board[0][1] && P board[0][2]) ||
  (P board[1][0] && P board[1][1] && P board[1][2]) ||
  (P board[2][0] && P board[2][1] && P board[2][2])

def GameState.checkForCols (state : GameState) (P : Cell → Bool) : Bool :=
  let board := state.board
  (P board[0][0] && P board[1][0] && P board[2][0]) ||
  (P board[0][1] && P board[1][1] && P board[2][1]) ||
  (P board[0][2] && P board[1][2] && P board[2][2])

def GameState.checkForDiag (state : GameState) (P : Cell → Bool) : Bool :=
  let board := state.board
  (P board[0][0] && P board[1][1] && P board[2][2]) ||
  (P board[2][0] && P board[1][1] && P board[0][2])

def GameState.checkForLines (state : GameState) (P : Cell → Bool) : Bool :=
  state.checkForRows P ||
  state.checkForCols P ||
  state.checkForDiag P

def GameState.result (state : GameState) : Result :=
  let xwin : Bool := state.checkForLines (· == Cell.x)
  let owin := state.checkForLines (· == Cell.o)
  let draw := state.unused.isEmpty
  if xwin then
    .xwin
  else if owin then
    .owin
  else if draw then
    .draw
  else
    .progress

def main : IO Unit := do
  let mut gameState := GameState.empty
  let mut result : Result := .progress

  while true do
    gameState.display

    let input ← getUserInput
    let some yourPos := parsePosition input |
      IO.println "1から9の数字を入力してください"
      continue
    if !gameState.allow yourPos then
      IO.println "その場所には着手できません"
      continue
    gameState := gameState.update yourPos Cell.x

    result := gameState.result
    if result != .progress then
      break

    let cpuPos ← getRandomPos gameState
    gameState := gameState.update cpuPos Cell.o

    result := gameState.result
    if result != .progress then
      break

  gameState.display
  match result with
  | .xwin =>
    IO.println "x の勝ち"
  | .owin =>
    IO.println "o の勝ち"
  | .draw =>
    IO.println "引き分け"
  | _ => unreachable!
