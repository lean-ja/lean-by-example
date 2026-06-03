
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

/-- ゲームが持っている、盤面の状態 -/
abbrev Board := Vector (Vector Cell 3) 3

def Board.empty : Board :=
  let row := #v[Cell.empty, Cell.empty, Cell.empty]
  let board := #v[row, row, row]
  board

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
def Board.display (board : Board) (indentSize : Nat := 5) : IO Unit := do
  let indent := " ".pushn ' ' indentSize
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
def Board.unused (board : Board) : Array Position :=
  let flatBoard := board.flatten
  let unusedIdxes := flatBoard.zipIdx
    |>.toArray
    |>.filter (fun (cell, _idx) => cell == .empty)
    |>.map (fun (_cell, idx) => idx)
  unusedIdxes.map Position.build!

/-- ゲームの盤面の状態を更新して、新しい盤面を返す
既に着手済みの場所に置こうとすると失敗し、`panic!` する -/
def Board.update! (board : Board) (pos : Position) (c : Cell) : Board :=
  if !pos ∈ board.unused then
    panic! "[Board.update] the position is already used"
  else
    let oldRow := board[pos.x]
    let newRow := oldRow.set pos.y c
    let newBoard := board.set pos.x newRow
    newBoard

def Array.getRandom! {α : Type} [Inhabited α] (xs : Array α) : IO α := do
  let idx ← IO.rand 0 (xs.size - 1)
  return xs[idx]!

/-- 未着手の場所をランダムに選ぶ -/
def getRandomPos (board : Board) : IO Position := do
  let unused := board.unused
  let pos ← unused.getRandom!
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

def Line.check (line : Line) (board : Board) (P : Cell → Bool) : Bool :=
  line.all (fun pos => P (board[pos.x][pos.y]))

def Board.checkForLines (board : Board) (P : Cell → Bool) : Bool :=
  allLines.any (fun line => line.check board P)

def Board.result (board : Board) : Result :=
  let xwin : Bool := board.checkForLines (· == Cell.x)
  let owin := board.checkForLines (· == Cell.o)
  let draw := board.unused.isEmpty
  if xwin then
    .xwin
  else if owin then
    .owin
  else if draw then
    .draw
  else
    .progress

partial def getUserHand (board : Board) : IO Position := do
  let input ← getUserRawInput
  let some pos := parsePosition input |
    IO.println "0から8の数字を入力してください"
    board.display
    getUserHand board

  if !(pos ∈ board.unused) then
    IO.println "その場所には着手できません"
    board.display
    getUserHand board
  else
    return pos

def main : IO Unit := do
  let mut board := Board.empty
  let mut result : Result := .progress

  while true do
    board.display

    let yourPos ← getUserHand board
    board := board.update! yourPos Cell.x

    result := board.result
    if result != .progress then
      break

    let cpuPos ← getRandomPos board
    board := board.update! cpuPos Cell.o

    result := board.result
    if result != .progress then
      break

  board.display
  match result with
  | .xwin =>
    IO.println "x の勝ち"
  | .owin =>
    IO.println "o の勝ち"
  | .draw =>
    IO.println "引き分け"
  | _ => unreachable!
