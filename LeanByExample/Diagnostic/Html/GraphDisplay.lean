import ProofWidgets

open ProofWidgets Jsx GraphDisplay

/-- `Edge` を作る -/
def mkEdge (st : String × String) : Edge := {source := st.1, target := st.2}

/-- 文字列として与えられたラベルから `Vertex` を作る -/
def mkVertex (id : String) : Vertex := {id := id}

-- 有向グラフを表示する
#html
  <GraphDisplay
    vertices={#["a", "b", "c", "d", "e"].map mkVertex}
    edges={#[("a", "b"), ("b", "c"), ("c", "d"), ("d", "e"), ("e", "a")].map mkEdge}
  />
