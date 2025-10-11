import ProofWidgets

open ProofWidgets Svg

/-- デフォルトの表示領域(Frame) -/
def defaultFrame : Frame := {
  xmin := 0 -- 左下隅の x 座標
  ymin := 0 -- 左下隅の y 座標
  width := 450 -- 横方向のピクセル数
  height := 450 -- 縦方向のピクセル数
  xSize := 450 -- width と同じ値なので、ピクセル数と座標の値は一致
}

/-- ノードを描画するときの円の半径 -/
def radius := 16

/-- ノードを描画するときの円の塗りつぶし色(RGB) -/
def fillColor := (0.74, 0.87, 1.0)

/-- ノードのラベルのフォントサイズ -/
def fontsize := 14

/-- ノードのラベルの色(RGB) -/
def textColor := (0.0, 0.0, 0.0)

/-- 位置情報を付加したノードのデータ -/
structure NodePos where
  /-- ノードのx座標(右に行くほど大きい) -/
  x : Float
  /-- ノードのy座標(下に行くほど大きい) -/
  y : Float
  /-- ラベル -/
  label : String

/-- 上面と下面を反転して計測したy座標 -/
def NodePos.y_inv (self : NodePos) : Float :=
  defaultFrame.height.toFloat - self.y

/-- ノード（円とラベル）を作成する -/
def createNodeElement (node : NodePos) : Array (Element defaultFrame) :=
  let circle := circle (node.x, node.y_inv) (.px radius)
    |>.setFill fillColor
  let adjust := fontsize.toFloat * 0.35 -- ラベルの位置調整用
  let text := text (node.x - adjust, node.y_inv - adjust) node.label (.px fontsize)
    |>.setFill textColor
  #[circle, text]

/-- `createNodeElement` の表示結果をテストするための関数 -/
def createNodeHtml (node : NodePos) : Html :=
  let svg : Svg defaultFrame := { elements := createNodeElement node }
  svg.toHtml

-- ノードの描画テスト
#html createNodeHtml (node := { x := 150, y := 30, label := "A" })

/-- エッジの色(RGB) -/
def edgeColor := (50.0, 50.0, 50.0)

/-- エッジの太さ(ピクセル) -/
def edgeWidth := 2

/-- エッジ（ノードの親子関係）を作成する -/
def createEdgeElement (parent child : NodePos) : Element defaultFrame :=
  line (parent.x, parent.y_inv) (child.x, child.y_inv)
  |>.setStroke edgeColor (.px edgeWidth)

/-- `createEdgeElement` の表示結果をテストするための関数 -/
def createEdgeHtml (parent child : NodePos) : Html :=
  let svg : Svg defaultFrame := { elements := #[createEdgeElement parent child] }
  svg.toHtml

#html createEdgeHtml
  (parent := { x := 150, y := 30, label := "A" })
  (child := { x := 100, y := 80, label := "B" })

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

def BinTree.toElementsFromLayout (tree : BinTree (α × (Nat × Nat))) (step : Float) : Array (Svg.Element defaultFrame) :=
  let nodes := tree.toNodes
    |>.map (NodePos.ofPair (step := step))
    |>.map createNodeElement
    |>.flatten
  let edges := tree.toEdges
    |>.map (fun ((v1, x1, y1), (v2, x2, y2)) => (NodePos.ofPair (v1, x1, y1) step, NodePos.ofPair (v2, x2, y2) step))
    |>.map (fun (parent, child) => createEdgeElement parent child)
  edges ++ nodes

/-- ２分木の描画情報が与えられたときに、それを SVG 画像として描画する -/
def BinTree.toHtmlFromLayout (tree : BinTree (α × (Nat × Nat))) (step := 30.0) : Html :=
  let svg : Svg defaultFrame := { elements := tree.toElementsFromLayout step }
  svg.toHtml

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
  BinTree.toHtmlFromLayout treeLayout

/-- ２分木のレイアウト情報が渡されたときに、各ノードのレイアウト位置を一様にずらす -/
def BinTree.shift {β γ : Type} (tree : BinTree (α × (β × β))) (shiftFn : β × β → γ × γ) : BinTree (α × (γ × γ)) :=
  match tree with
  | .empty => .empty
  | .node (a, (x, y)) left right =>
    let (x', y') := shiftFn (x, y)
    .node (a, (x', y')) (shift left shiftFn) (shift right shiftFn)

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
  BinTree.toHtmlFromLayout (BinTree.layout tree)
