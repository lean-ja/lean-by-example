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

#guard Array.reshape (m := 2) (n := 3) #[1, 2, 3, 4, 5, 6] = #[#[1, 2, 3], #[4, 5, 6]]

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
    some Player.x, some Player.o, none,
    none, some Player.x, none,
    some Player.o, none, some Player.x
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
  /-- x を持っているプレイヤーの勝ち -/
  | xwin
  /-- o を持っているプレイヤーの勝ち -/
  | owin
  /-- 引き分け -/
  | draw
deriving BEq

/-- 勝敗判定に使われるラインを全部列挙したもの -/
def allLines : Array (Array Nat) :=
  let row0 := #[0, 1, 2]
  let row1 := #[3, 4, 5]
  let row2 := #[6, 7, 8]
  let col0 := #[0, 3, 6]
  let col1 := #[1, 4, 7]
  let col2 := #[2, 5, 8]
  let diag1 := #[0, 4, 8]
  let diag2 := #[2, 4, 6]
  #[row0, row1, row2, col0, col1, col2, diag1, diag2]

def checkLine (line : Array Nat) (board : Board) (P : Player → Bool) : Bool :=
  line.all (fun pos =>
    let player? := board[pos]!
    (P <$> player?).getD false
  )

def Board.checkForLines (board : Board) (P : Player → Bool) : Bool :=
  allLines.any (checkLine · board P)

-- Player の BEq インスタンスを自動生成する
deriving instance BEq for Player

/-- 盤面の勝敗判定をする。
まだゲームが続けられる場合は `none` を返す。 -/
def Board.result? (board : Board) : Option Result :=
  let xwin := board.checkForLines (· == Player.x)
  let owin := board.checkForLines (· == Player.o)
  let draw := board.all (·.isSome)
  if xwin then
    some .xwin
  else if owin then
    some .owin
  else if draw then
    some .draw
  else
    none

#guard
  let board : Board := #v[
    some Player.x, some Player.o, none,
    none, some Player.x, none,
    some Player.o, none, some Player.x
  ]
  board.result? == some Result.xwin

#guard
  let board : Board := #v[
    some Player.x, some Player.o, none,
    none, none, none,
    some Player.o, none, some Player.x
  ]
  board.result? == none
