import ProofWidgets

open ProofWidgets Svg

/-- デフォルトの表示領域(Frame) -/
private def defaultFrame : Frame := {
  xmin := 0 -- 左下隅の x 座標
  ymin := 0 -- 左下隅の y 座標
  width := 1000 -- 横方向のピクセル数
  height := 1000 -- 縦方向のピクセル数
  xSize := 1000 -- width と同じ値なので、ピクセル数と座標の値は一致
}

/-- 描画に関する設定 -/
structure RenderConfig where
  /-- ノードを描画するときの円の半径 -/
  radius : Nat := 16
  /-- ノードを描画するときの円の塗りつぶし色(RGB) -/
  fillColor : (Float × Float × Float) := (0.74, 0.87, 1.0)
  /-- ノードのラベルのフォントサイズ -/
  fontsize : Nat := 14
  /-- ノードのラベルの色(RGB) -/
  textColor : (Float × Float × Float) := (0.0, 0.0, 0.0)
  /-- エッジの色(RGB) -/
  edgeColor : (Float × Float × Float) := (50.0, 50.0, 50.0)
  /-- エッジの太さ(ピクセル) -/
  edgeWidth : Nat := 2
  /-- ノード間の水平・垂直間隔の基準値 -/
  step := 30.0

/-- `RenderConfig`を読み取りできる計算文脈を表すモナド -/
abbrev RenderM := ReaderM RenderConfig

/-- 位置情報を付加したノードのデータ -/
structure NodePos where
  /-- ノードのx座標(右に行くほど大きい) -/
  x : Float
  /-- ノードのy座標(下に行くほど大きい) -/
  y : Float
  /-- ラベル -/
  label : String

/-- 上面と下面を反転して計測したy座標 -/
private def NodePos.y_inv (self : NodePos) (f : Frame) : Float :=
  f.height.toFloat - self.y

/-- ノード（円とラベル）を作成する -/
private def createNodeElements (node : NodePos) (f : Frame) : RenderM (Array (Element f)) := do
  let radius := (← read).radius
  let fillColor := (← read).fillColor
  let fontsize := (← read).fontsize
  let textColor := (← read).textColor

  let circle := circle (node.x, node.y_inv f) (.px radius)
    |>.setFill fillColor
  let adjust := fontsize.toFloat * 0.35 -- ラベルの位置調整用
  let text := text (node.x - adjust, node.y_inv f - adjust) node.label (.px fontsize)
    |>.setFill textColor
  return #[circle, text]

/-- ノードの描画テスト用の関数 -/
private def createNodeHtml (node : NodePos) (f : Frame) : RenderM Html := do
  let elements ← createNodeElements node f
  let svg : Svg f := { elements := elements }
  return svg.toHtml

#html ReaderT.run (r := {}) <|
  createNodeHtml (f := defaultFrame) (node := { x := 150, y := 30, label := "A" })

/-- エッジ（ノードの親子関係）を作成する -/
private def createEdgeElement (parent child : NodePos) (f : Frame) : RenderM (Element f) := do
  let edgeColor := (← read).edgeColor
  let edgeWidth := (← read).edgeWidth
  let element := line (parent.x, parent.y_inv f) (child.x, child.y_inv f)
    |>.setStroke edgeColor (.px edgeWidth)
  return element

/-- エッジの描画テスト用の関数 -/
private def createEdgeHtml (parent child : NodePos) (f : Frame) : RenderM Html := do
  let element ← createEdgeElement parent child f
  let svg : Svg f := { elements := #[element] }
  return svg.toHtml

#html ReaderT.run (r := {}) <| createEdgeHtml
  (parent := { x := 150, y := 30, label := "A" })
  (child := { x := 100, y := 80, label := "B" })
  (f := defaultFrame)

/-- (ラベル付きの)二分木 -/
inductive BinTree (α : Type) where
  /-- 空の木 -/
  | empty
  /-- ノード -/
  | node (val : α) (left right : BinTree α)

variable {α : Type} [ToString α]

/-- 二分木をノードの配列に変換する。 -/
def BinTree.toNodes (tree : BinTree α) : Array α :=
  match tree with
  | .empty => #[]
  | .node val left right => #[val] ++ (left.toNodes ++ right.toNodes)

/-- 二分木のエッジを配列にする。(親, 子) のペアにして返すことに注意。 -/
def BinTree.toEdges {β : Type} (tree : BinTree β) : Array (β × β) :=
  match tree with
  | .empty => #[]
  | .node a left right =>
    let leftEdges :=
      match left with
      | .empty => #[]
      | .node b _ _ => (toEdges left).push (a, b)
    let rightEdges :=
      match right with
      | .empty => #[]
      | .node c _ _ => (toEdges right).push (a, c)
    leftEdges ++ rightEdges

/-- ３つ組データを構造体の項に変換する -/
def NodePos.ofPair (p : α × Nat × Nat) (step : Float) : NodePos :=
  let (label, x, y) := p
  { x := x.toFloat * step, y := y.toFloat * step, label := toString label }

/-- ２分木の描画情報が与えられたときに、それを SVG 画像として描画する -/
def BinTree.render (tree : BinTree (α × (Nat × Nat))) (f : Frame := defaultFrame) (cfg : RenderConfig := {}) : Html :=
  let html : RenderM Html := do
    let step := (← read).step
    let nodesArray ← tree.toNodes
      |>.map (NodePos.ofPair (step := step))
      |>.mapM (fun node => createNodeElements node f)
    let nodes := nodesArray.flatten
    let edgesArray ← tree.toEdges
      |>.map (fun (x1, x2) => (NodePos.ofPair x1 step, NodePos.ofPair x2 step))
      |>.mapM (fun (parent, child) => createEdgeElement parent child f)
    let svg : Svg f := { elements := edgesArray ++ nodes }
    return svg.toHtml
  ReaderT.run html cfg

/-- 二分木の葉 -/
def BinTree.leaf (val : α) : BinTree α :=
  .node val .empty .empty

-- 二分木の描画テスト
-- レイアウト情報を手動で与えて描画している
#html
  let treeLayout := BinTree.node ("A", (2, 1))
    (.leaf ("B", (1, 2)))
    (.node ("C", (4, 2))
      (.leaf ("D", (3, 3)))
      (.leaf ("E", (5, 3))))
  BinTree.render treeLayout

/-- 2分木の各要素に一様に関数を適用する -/
def BinTree.map {α β : Type} (f : α → β) (tree : BinTree α) : BinTree β :=
  match tree with
  | .empty => .empty
  | .node val left right =>
    .node (f val) (map f left) (map f right)

/-- `BinTree`は関手 -/
instance : Functor BinTree where
  map := BinTree.map

/-- ２分木のレイアウト情報が渡されたときに、各ノードのレイアウト位置を一様にずらす -/
def BinTree.shift {β γ : Type} (tree : BinTree (α × β)) (shiftFn : β → γ) : BinTree (α × γ) :=
  (fun (a, pos) => (a, shiftFn pos)) <$> tree

/-- ２分木の描画幅。二分木を描画したときに何グリッド占めるか。 -/
def BinTree.width (tree : BinTree α) : Nat :=
  tree.toNodes.size - 1

/-- 二分木のレイアウトを計算する関数 -/
def BinTree.layout (tree : BinTree α) : BinTree (α × (Nat × Nat)) :=
  match tree with
  | .empty => .empty
  | .node a .empty .empty =>
    .node (a, (1, 1)) .empty .empty
  | .node a .empty right =>
    let rightLayout := layout right
    let rightShifted := rightLayout.shift (fun (x, y) => (x + 1, y + 1))
    .node (a, (1, 1)) .empty rightShifted
  | .node a left .empty =>
    let leftLayout := layout left
    let leftShifted := leftLayout.shift (fun (x, y) => (x, y + 1))
    .node (a, (left.width + 2) * 1, 1) leftShifted .empty
  | .node a left right =>
    let leftLayout := layout left
    let rightLayout := layout right
    let leftShifted := leftLayout.shift (fun (x, y) => (x, y + 1))
    let rightShifted := rightLayout.shift (fun (x, y) => (x + (left.width + 2) * 1, y + 1))
    .node (a, ((left.width + 2) * 1, 1)) leftShifted rightShifted

-- 二分木の描画テスト
-- 二分木からレイアウト情報を計算し、それを元に描画している
#html
  let tree := BinTree.node "A"
    (BinTree.leaf "B")
    (BinTree.node "C"
      (BinTree.leaf "D")
      (BinTree.leaf "E"))
  BinTree.render tree.layout
