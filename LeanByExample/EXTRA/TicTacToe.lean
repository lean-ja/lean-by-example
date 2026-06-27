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
def Board := Vector (Option Player) 9

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

#eval Board.display Board.initial

#eval
  let board : Board := #v[
    some Player.x, some Player.o, none,
    none, some Player.x, none,
    some Player.o, none, some Player.x
  ]
  Board.display board
