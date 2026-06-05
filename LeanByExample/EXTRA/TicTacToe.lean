/- # 三目並べ

以下は三目並べを CLI ゲームとして実装する例です。CPU は単にランダムに手を選ぶだけなので、簡単に勝てると思います。
-/

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

/-- ゲームの盤面 -/
abbrev Board := Array Cell

def Board.empty : Board :=
  Array.replicate 9 Cell.empty

/-- ユーザー入力を受け取る -/
def getUserRawInput : IO String := do
  IO.print "> "
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  return input.trimAscii.copy

def parsePosition (input : String) : Option Nat :=
  let num? := input.toNat?
  match num? with
  | none => none
  | some num =>
    if num < 9 then
      num
    else
      none

/-- テキストが灰色で表示されるようにする -/
def grayText (s : String) : String :=
  s!"\x1b[90m{s}\x1b[0m"

def Cell.display (c : Cell) (pos : Nat) : String :=
  match c with
  | .empty => grayText <| toString pos
  | _ => toString c

/-- ゲームの盤面の状態を表示する -/
def Board.display (board : Board) (indentSize : Nat := 5) : IO Unit := do
  let indent := " ".pushn ' ' indentSize
  IO.println s!"{indent}+--+--+--+"
  for pos in [0:9] do
    if pos % 3 == 0 then
      IO.print indent
    let displayText := board[pos]!.display pos
    IO.print s!"| {displayText}"
    if pos % 3 == 2 then
      IO.println "|"
      IO.println s!"{indent}+--+--+--+"

/-- 未着手のセルを列挙する -/
def Board.unused (board : Board) : Array Nat :=
  List.range 9 |>.toArray |>.filter (fun pos => board[pos]! == .empty)

/-- ゲームの盤面の状態を更新して、新しい盤面を返す
既に着手済みの場所に置こうとすると失敗し、`panic!` する -/
def Board.update (board : Board) (pos : Nat) (c : Cell) : Board :=
  if board[pos]! != .empty then
    panic! "[Board.update] the position is already used"
  else
    board.set! pos c

def Array.getRandom [Inhabited α] (xs : Array α) : IO α := do
  let idx ← IO.rand 0 (xs.size - 1)
  return xs[idx]!

/-- 未着手の場所をランダムに選ぶ -/
def getRandomPos (board : Board) : IO Nat := do
  let unused := board.unused
  let pos ← unused.getRandom
  return pos

inductive Result where
  /-- x を持っているプレイヤーの勝ち -/
  | xwin
  /-- o を持っているプレイヤーの勝ち -/
  | owin
  /-- 引き分け -/
  | draw
deriving BEq

abbrev Line := Array Nat

def allLines : Array Line :=
  let row0 : Line := #[0, 1, 2]
  let row1 : Line := #[3, 4, 5]
  let row2 : Line := #[6, 7, 8]
  let col0 : Line := #[0, 3, 6]
  let col1 : Line := #[1, 4, 7]
  let col2 : Line := #[2, 5, 8]
  let diag1 : Line := #[0, 4, 8]
  let diag2 : Line := #[2, 4, 6]
  #[row0, row1, row2, col0, col1, col2, diag1, diag2]

def Line.check (line : Line) (board : Board) (P : Cell → Bool) : Bool :=
  line.all (fun pos => P (board[pos]!))

def Board.checkForLines (board : Board) (P : Cell → Bool) : Bool :=
  allLines.any (fun line => line.check board P)

def Board.result? (board : Board) : Option Result :=
  let xwin : Bool := board.checkForLines (· == Cell.x)
  let owin := board.checkForLines (· == Cell.o)
  let draw := board.unused.isEmpty
  if xwin then
    some .xwin
  else if owin then
    some .owin
  else if draw then
    some .draw
  else
    none

partial def getUserHand (board : Board) : IO Nat := do
  let input ← getUserRawInput
  let some pos := parsePosition input |
    IO.println "0から8の数字を入力してください"
    board.display
    getUserHand board

  if board[pos]! != .empty then
    IO.println "その場所には着手できません"
    board.display
    getUserHand board
  else
    return pos

def main : IO Unit := do
  let mut board := Board.empty
  let mut result? : Option Result := none

  while true do
    board.display

    let yourPos ← getUserHand board
    board := board.update yourPos Cell.x

    result? := board.result?
    if result?.isSome then
      break

    let cpuPos ← getRandomPos board
    board := board.update cpuPos Cell.o

    result? := board.result?
    if result?.isSome then
      break

  board.display
  let some result := result? |
    unreachable!
  match result with
  | .xwin =>
    IO.println "x の勝ち"
  | .owin =>
    IO.println "o の勝ち"
  | .draw =>
    IO.println "引き分け"
