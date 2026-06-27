import Plausible

/- # 三目並べ

Lean で、CLI ゲームとして三目並べを実装してみましょう。

## 盤面を定義する

まずは三目並べの盤面を作ってみます。盤面がどのようなものが考えてみると、次のようなものです。

1. 盤面は9マスある
2. 盤面の各マスは、各プレイヤーの着手したマークが入っているか、あるいは空であるかどちらか
3. 最初は全てのマスが空

盤面は 3×3 の二次元的な構造を持っているのですが、サイズが小さいので二次元配列として持つよりも一次元配列として持った方が簡単です。そこで、盤面は長さ9のベクトル(長さが固定された配列)として持つことにします。
-/

/-- プレイヤー -/
inductive Player where
  /-- 先手 -/
  | x
  /-- 後手 -/
  | o

/-- 盤面 -/
abbrev Board := Vector (Option Player) 9

/-- 盤面の初期状態 -/
def Board.initial : Board := Vector.replicate 9 none

/- ## 盤面を表示する

次に、盤面を表示できるようにしましょう。既に埋まっている部分はそのまま表示し、空の部分にはユーザが着手場所を選ぶときわかりやすいように、番号を振って表示することにします。
-/

/-- Player を文字列として表示する。
数字の `0` と `Player.o` の区別がつきやすいようにしてある -/
instance : ToString Player where
  toString := fun p =>
    match p with
    | .x => "×"
    | .o => "●"

/-- 配列を二次元配列に変換する。
サイズが期待と異なる場合は `panic!` を呼ぶ -/
def Array.reshape (m n : Nat) (xs : Array α) : Array (Array α) :=
  if xs.size ≠ m * n then
    panic! s!"{decl_name%}: size mismatch"
  else
    Array.range m |>.map (fun i => xs.extract (n * i) (n * (i + 1)))

#guard
  let actual := Array.reshape (m := 2) (n := 3) #[1, 2, 3, 4, 5, 6]
  let expected := #[#[1, 2, 3], #[4, 5, 6]]
  actual = expected

#test ∀ α : Type, ∀ m n : Nat, ∀ xs : Array α,
  xs.size = m * n → (Array.reshape m n xs).flatMap id = xs

/-- 配列の要素の間に区切りを挿入する -/
def Array.intersperse (xs : Array α) (sep : α) : Array α :=
  match xs.toList with
  | [] => #[]
  | x :: rest =>
    rest.foldl (fun acc y => acc ++ #[sep, y]) #[x]

#guard Array.intersperse #[1, 2, 3] 0 = #[1, 0, 2, 0, 3]

#test ∀ α : Type, ∀ xs : Array α, ∀ sep : α,
  (Array.intersperse xs sep).size = xs.size * 2 - 1

/-- 盤面を表示するための補助関数 -/
def Board.toStrArray (b : Board) : Array String :=
  let rawStrArray := b.toArray
    |>.zipIdx
    |>.map (fun (p?, idx) =>
      match p? with
      | none => toString idx
      | some p => toString p)
  let rows2D := rawStrArray.reshape (m := 3) (n := 3)
  let rows1D := rows2D.map (fun row =>
    let inner := String.intercalate " | " row.toList
    s!"| {inner} |"
  )
  let boader := "+---+---+---+"
  #[boader] ++ rows1D.intersperse boader ++ #[boader]

/-- 盤面を表示する関数。
IO 部分を少なくするため、補助関数を薄く包むだけにしてある -/
def Board.display (b : Board) : IO Unit := do
  for str in b.toStrArray do
    IO.println str

-- テスト用に、盤面を簡便に構成するための補助定義
def X : Option Player := Player.x
def O : Option Player := Player.o
def E : Option Player := none

/--
info:
+---+---+---+
| × | ● | 2 |
+---+---+---+
| 3 | × | 5 |
+---+---+---+
| ● | 7 | × |
+---+---+---+
-/
#guard_msgs in --#
#eval
  let board : Board := #v[
    X, O, E,
    E, X, E,
    O, E, X
  ]
  Board.display board

/- ## 盤面の勝敗判定をする

次に、盤面の勝敗判定を実装してみます。勝敗は、以下の３通りのどれかになります。

1. 引き分け
2. `X` を持っているプレイヤーの勝ち
3. `O` を持っているプレイヤーの勝ち
-/

/-- ゲームの結果 -/
inductive Result where
  /-- `winner` を持っているプレイヤーの勝ち -/
  | win (winner : Player)
  /-- 引き分け -/
  | draw

/-- 勝敗判定に使われるライン -/
abbrev Line := Vector (Fin 9) 3

/-- 勝敗判定に使われるラインを全部列挙したもの -/
def allLines : Array Line :=
  let row0 := #v[0, 1, 2]
  let row1 := #v[3, 4, 5]
  let row2 := #v[6, 7, 8]
  let col0 := #v[0, 3, 6]
  let col1 := #v[1, 4, 7]
  let col2 := #v[2, 5, 8]
  let diag1 := #v[0, 4, 8]
  let diag2 := #v[2, 4, 6]
  #[row0, row1, row2, col0, col1, col2, diag1, diag2]

def checkLine (line : Line) (board : Board) (P : Player → Bool) : Bool :=
  line.all (fun pos =>
    let player? := board[pos]
    (P <$> player?).getD false
  )

def Board.checkForLines (board : Board) (P : Player → Bool) : Bool :=
  allLines.any (checkLine · board P)

-- Player 等の DecidableEq インスタンスを自動生成する
deriving instance DecidableEq for Player, Result

/-- 盤面の勝敗判定をする。
まだゲームが続けられる場合は `none` を返す。 -/
@[grind =]
def Board.result? (board : Board) : Option Result :=
  let wins : Player → Bool :=
    fun p => board.checkForLines (· = p)
  let draw := board.all (·.isSome)
  if wins .x then
    some <| .win (Player.x)
  else if wins .o then
    some <| .win (Player.o)
  else if draw then
    some .draw
  else
    none

#guard
  let board : Board := #v[
    X, O, X,
    O, X, O,
    O, X, X
  ]
  board.result? = some (Result.win Player.x)

#guard
  let board : Board := #v[
    X, O, E,
    E, E, E,
    O, E, X
  ]
  board.result? = none

/- ## 着手できるようにする

盤面のまだ着手されていない場所を選んで、着手ができるようにします。
-/

/-- 盤面上の場所 -/
abbrev Position := Fin 9

/-- 盤面上の場所 `move` にプレイヤー `p` が手を置き、新しい盤面を返す。
ただし、既に着手されている場合は `Except.error` を返す。 -/
def Board.place! (board : Board) (move : Position) (p : Player) : Except String Board :=
  match board[move] with
  | some _ => Except.error s!"{decl_name%}: position {move} is already occupied"
  | none => Except.ok (board.set move (some p))

#guard show Bool from Id.run do
  let board : Board := #v[
    X, O, E,
    E, E, E,
    O, E, X
  ]
  let .ok actual := board.place! 2 Player.x
    | return false
  let expected : Board := #v[
    X, O, X,
    E, E, E,
    O, E, X
  ]
  actual == expected

#guard
  let board : Board := #v[
    X, O, E,
    E, E, E,
    O, E, X
  ]
  !(board.place! 1 Player.x).toBool

/-
何か着手するたびに `Except` が返ってくるのを回避することができるように、「着手箇所が空であることの証明」を引数に持たせるバージョンも定義しておきましょう。
-/

/-- 合法な着手 -/
structure LegalMove (b : Board) where
  /-- 盤面 `b` 上の着手箇所 -/
  move : Position
  /-- 着手箇所が空であることの証明 -/
  proof : b[move] = none

/-- `LegalMove` の項を作るための補助関数。
`move` が具体的な数であれば、`decide` により自動的に証明が生成されて通る。 -/
def Board.legalCheck (b : Board) (move : Position) (h : b[move] = none := by decide) : LegalMove b :=
  { move := ⟨move, by simp⟩, proof := h }

/-- 合法な着手箇所が与えられたときに、そこに着手した新しい盤面を返す。-/
def Board.place (board : Board) (move : LegalMove board) (p : Player) : Board :=
  board.set move.move (some p)

/--
info:
+---+---+---+
| × | ● | × |
+---+---+---+
| 3 | 4 | 5 |
+---+---+---+
| ● | 7 | × |
+---+---+---+
-/
#guard_msgs in --#
#eval
  let board : Board := #v[
    X, O, E,
    E, E, E,
    O, E, X
  ]
  let legalMove := board.legalCheck 2
  let newBoard := board.place legalMove Player.x
  Board.display newBoard

/-
将来的に「その盤面において合法な手を全列挙する」という関数が欲しくなることが予想されるので、それも実装しておきます。
-/

/-- 合法な着手箇所を全列挙する -/
def Board.legalMoves (b : Board) : List (LegalMove b) :=
  List.finRange 9 |>.filterMap (fun pos =>
    match h : b[pos] with
    | none => some { move := pos, proof := h }
    | some _ => none
  )

#guard
  let board : Board := #v[
    X, O, E,
    E, E, E,
    O, E, X
  ]
  board.legalMoves.map (fun legalMove => legalMove.move.val) = [2, 3, 4, 5, 7]

/- ## 補題の用意

後で必要になるので、合法手を全列挙する関数 `legalMoves` に関する補題をいくつか用意しておきます。おもに「ゲームが進行中なら、合法な手が存在する」というのが欲しい命題です。
-/

/-- ゲームが進行中 -/
@[grind =]
def Board.inProgress (board : Board) : Bool :=
  board.result? = none

theorem Board.noLegalMove_iff_allSome (board : Board) : board.legalMoves = [] ↔ board.all Option.isSome := by
  unfold Board.legalMoves
  simp only [
    Fin.getElem_fin,
    List.filterMap_eq_nil_iff,
    List.mem_finRange,
    forall_const,
    Vector.all_eq_true
  ]
  constructor
  · intro h pos hpos
    specialize h ⟨pos, hpos⟩
    grind
  · intro h
    grind

grind_pattern Board.noLegalMove_iff_allSome => board.legalMoves, []

theorem Board.notInProgress_of_allSome (board : Board) (h : board.all Option.isSome) : ¬board.inProgress := by
  unfold Board.inProgress
  simp [Board.result?]
  grind only [= Vector.all_eq]

grind_pattern Board.notInProgress_of_allSome => board.all Option.isSome, board.inProgress

theorem Board.legalMoveExists (board : Board) (h : board.inProgress) : board.legalMoves ≠ [] := by
  intro hEmpty
  have : board.all Option.isSome := by grind
  grind only [usr notInProgress_of_allSome]

grind_pattern Board.legalMoveExists => board.legalMoves, board.inProgress

/- ## CPU の思考アルゴリズムの実装

次はいよいよ、CPU の思考アルゴリズムを実装します。単に「ランダムに手を選ぶ」ような CPU を実装しても良いのですが、せっかくなので賢い CPU を実装してみます。次のような方針で実装しましょう。

1. 次に着手できる場所をすべてリストアップする。
1. 各盤面の評価値（自分が有利なのか不利なのかを表す値）を計算して、最も評価値が高いものを選ぶ。

### 評価値の計算

問題は評価値の計算方法ですが、以下のような方針で計算することができます。

1. 自分が勝ちの局面では `10` 点
2. 相手が勝ちの局面では `-10` 点
3. 引き分けの場面では `0` 点
4. それ以外の局面では、「自分も相手も最善手を打った場合にどうなるか」を考えて決める。
  具体的には、次の手で到達可能な局面をまずすべて調べる。
  そして自分の手番なら評価値が最大になる手を選んで、その評価値を採用する。
  相手の手番なら自分から見た評価値が最小になる手を選んで、その評価値を採用する。
5. なるべく短い手順で勝利するほど、高い評価値を与えるようにする

これを素直に実装すると、[相互再帰関数](#{root}/Declarative/Mutual.md) になります。
-/

/-- そのプレイヤーの対戦相手 -/
def Player.opponent : Player → Player
  | .x => .o
  | .o => .x

/-- 現在手番を持っているプレイヤー -/
def Board.current (b : Board) : Player :=
  let xCount := b.count (some Player.x)
  let oCount := b.count (some Player.o)
  if xCount ≤ oCount then
    Player.x
  else
    Player.o

/-- 盤面の複雑さの指標。
なるべく短い手順で勝利するほど、高い評価値を与えるために使用 -/
def Board.depth (b : Board) : Nat :=
  b.toArray
    |>.filter Option.isSome
    |>.size

mutual

/-- この盤面で `p` が手番を持っている場合に、`p` から見た盤面の評価値 -/
partial def Board.maxScore (board : Board) (p : Player) : Int :=
  match h : board.result? with
  | some (Result.win winner) =>
    if winner = p then 10 - board.depth else board.depth - 10
  | some Result.draw => 0
  | none =>
    let nextMoves := board.legalMoves
    let nextBoards := nextMoves.map (board.place · p)
    let nextScores := nextBoards.map (fun b => Board.minScore b p)

    -- `List.max` 関数は空でないリストに対してしか使えないので、
    -- 空でないことを証明する必要がある。
    have h : nextScores ≠ [] := by
      have hMoves : nextMoves ≠ [] := by grind
      simpa [nextScores, nextBoards] using hMoves

    nextScores.max h

/-- この盤面で `p` の対戦相手が手番を持っている場合に、`p` から見た盤面の評価値 -/
partial def Board.minScore (board : Board) (p : Player) : Int :=
  match h : board.result? with
  | some (Result.win winner) =>
    if winner = p then 10 - board.depth else board.depth - 10
  | some Result.draw => 0
  | none =>
    let nextMoves := board.legalMoves
    let nextBoards := nextMoves.map (board.place · p.opponent)
    let nextScores := nextBoards.map (fun b => Board.maxScore b p)

    -- `List.min` 関数は空でないリストに対してしか使えないので、
    -- 空でないことを証明する必要がある。
    have h : nextScores ≠ [] := by
      have hMoves : nextMoves ≠ [] := by grind
      simpa [nextScores, nextBoards] using hMoves

    nextScores.min h

end -- mutual の終わり

/-- プレイヤー `p` から見た盤面の評価値 -/
def Board.score (board : Board) (p : Player) : Int :=
  if board.current = p then
    Board.maxScore board p
  else
    Board.minScore board p

-- `x` から見ると、既に勝っている場面
#guard
  let board : Board := #v[
    X, O, E,
    E, X, E,
    O, E, X
  ]
  Board.score board Player.x > 0

-- `x` から見ると、あと一手で勝てる必勝局面
#guard
  let board : Board := #v[
    X, O, E,
    E, E, E,
    O, E, X
  ]
  Board.score board Player.x > 0

-- `o` から見ると、あと一手で勝てる必勝局面
#guard
  let board : Board := #v[
    X, O, E,
    X, O, X,
    O, E, X
  ]
  Board.score board Player.o > 0

-- `o` が手番。
-- `o` は `x` の勝ちを防ぐことができるので引き分け
#guard
  let board : Board := #v[
    X, X, E,
    E, O, E,
    E, E, E
  ]
  Board.score board Player.x = 0

-- どちらの盤面も必勝局面だが、
-- 短い手順で勝利している方を高く評価する
#guard
  let board1 : Board := #v[
    O, E, E,
    X, X, X,
    O, E, E
  ]
  let board2 : Board := #v[
    O, X, E,
    X, X, E,
    O, E, E
  ]
  board1.score .x > board2.score .x && board2.score .x > 0

/- ### 手の選択の実装

評価値が手に入ったら、後はその評価値が最大になる手を選ぶだけです。実際に実装してみましょう。

ここでは、複数の候補手が同じ評価値を持つ場合は最も左上にある手を選ぶことにします。そうすると関数が決定的になってテストがやりやすいからです。
-/

@[simp, grind =]
theorem List.mergeSort_respect_nonEmpty (xs : List α) (f : α → α → Bool) :
    xs.mergeSort f = [] ↔ xs = [] := by
  simp only [← length_eq_zero_iff, length_mergeSort]

/-- 盤面 `board` において、プレイヤー `p` の最善手を探索する -/
def Board.selectBestMove (board : Board) (p : Player) (h : board.inProgress := by cbv) : LegalMove board :=
  let nextMoves := board.legalMoves
  let scoredMoves := nextMoves.map (fun move =>
    let newBoard := board.place move p
    let score := Board.score newBoard p
    (move, score)
  )
  let sortedScoredMoves := scoredMoves.mergeSort (fun (pos1, score1) (pos2, score2) =>
    score1 > score2 || (score1 = score2 && pos1.move.val < pos2.move.val)
  )

  -- `List.head` 関数は空でないリストに対してしか使えないので、空でないことを証明する必要がある。
  have h : sortedScoredMoves ≠ [] := by
    have hMoves : nextMoves ≠ [] := by
      grind only [usr legalMoveExists]
    have hScored : scoredMoves ≠ [] := by
      simpa [scoredMoves] using hMoves
    grind only [= List.mergeSort_respect_nonEmpty]

  let ⟨bestMove, score⟩ := sortedScoredMoves.head h
  bestMove

#guard show Bool from
  let board : Board := #v[
    X, O, E,
    E, E, E,
    O, E, X
  ]
  let move := Board.selectBestMove board Player.x
  let actual := board.place move Player.x
  let expected : Board := #v[
    X, O, E,
    E, X, E,
    O, E, X
  ]
  actual = expected
