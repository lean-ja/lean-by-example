
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
deriving Inhabited

def GameState.empty : GameState :=
  let row := #v[Cell.empty, Cell.empty, Cell.empty]
  let board := #v[row, row, row]
  { board := board }

/-- ユーザー入力を受け取る -/
def getUserRawInput : IO String := do
  IO.print "> "
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  return input.trimAscii.copy

structure Position where
  /-- 何行目かを表す -/
  x : Fin 3
  /-- 何列目かを表す -/
  y : Fin 3
deriving DecidableEq, Inhabited

def Position.flatten (pos : Position) : Nat :=
  pos.x.val * 3 + pos.y.val

def Position.next (pos : Position) : Position :=
  if hy : pos.y.val < 2 then
    let x : Fin 3 := ⟨pos.x, by grind⟩
    let y : Fin 3 := ⟨pos.y + 1, by grind⟩
    { x := x, y := y }
  else if hx : pos.x.val < 2 then
    let x : Fin 3 := ⟨pos.x + 1, by grind⟩
    let y : Fin 3 := 0
    { x := x, y := y }
  else
    { x := 0, y := 0}

def Position.build! (pos : Nat) : Position :=
  if h : pos ≤ 8 then
    let x : Fin 3 := ⟨pos / 3, by grind⟩
    let y : Fin 3 := ⟨pos % 3, by grind⟩
    { x := x, y := y }
  else
    panic! "[Position.build!] invalide argument error"

def parsePosition (input : String) : Option Position :=
  let num? := input.toNat?
  match num? with
  | none => none
  | some num =>
    if h : 0 ≤ num ∧ num ≤ 8 then
      let x : Fin 3 := ⟨num / 3, by grind⟩
      let y : Fin 3 := ⟨num % 3, by grind⟩
      some ⟨x, y⟩
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
  let mut pos : Position := { x := 0, y := 0}
  IO.println s!"{indent}+--+--+--+"
  for hi : i in [0:3] do
    let row := board[i]
    IO.print indent
    for hj : j in [0:3] do
      let displayText := row[j].display pos
      IO.print s!"| {displayText}"

      pos := pos.next

    IO.println s!"|"
    IO.println s!"{indent}+--+--+--+"

/-- 未着手のセルを列挙する -/
def GameState.unused (state : GameState) : Array Position :=
  let flatBoard := state.board.flatten
  let unusedIdxes := flatBoard.zipIdx
    |>.toArray
    |>.filter (fun (cell, _idx) => cell == .empty)
    |>.map (fun (_cell, idx) => idx)
  unusedIdxes.map Position.build!

/-- ゲームの盤面の状態を更新する。
既に着手済みの場所に置こうとすると失敗し、`panic!` する -/
def GameState.update (state : GameState) (pos : Position) (c : Cell) : GameState :=
  if !pos ∈ state.unused then
    panic! "[GameState.update] the position is already used"
  else
    let oldRow := state.board[pos.x]
    let newRow := oldRow.set pos.y c
    let newBoard := state.board.set pos.x newRow
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

abbrev Line := Vector Position 3

def allLines : Array Line :=
  let row0 : Line := #v[⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩]
  let row1 : Line := #v[⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩]
  let row2 : Line := #v[⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 2⟩]
  let col0 : Line := #v[⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩]
  let col1 : Line := #v[⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]
  let col2 : Line := #v[⟨0, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩]
  let diag1 : Line := #v[⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩]
  let diag2 : Line := #v[⟨0, 2⟩, ⟨1, 1⟩, ⟨2, 0⟩]
  #[row0, row1, row2, col0, col1, col2, diag1, diag2]

def Line.check (line : Line) (state : GameState) (P : Cell → Bool) : Bool :=
  line.all (fun pos => P (state.board[pos.x][pos.y]))

def GameState.checkForLines (state : GameState) (P : Cell → Bool) : Bool :=
  allLines.any (fun line => line.check state P)

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

partial def getUserHand (state : GameState) : IO Position := do
  let input ← getUserRawInput
  let some pos := parsePosition input |
    IO.println "1から9の数字を入力してください"
    state.display
    getUserHand state

  if !(pos ∈ state.unused) then
    IO.println "その場所には着手できません"
    state.display
    getUserHand state
  else
    return pos

def main : IO Unit := do
  let mut gameState := GameState.empty
  let mut result : Result := .progress

  while true do
    gameState.display

    let yourPos ← getUserHand gameState
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
