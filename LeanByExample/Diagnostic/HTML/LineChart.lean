import ProofWidgets

open Lean ProofWidgets Recharts

open scoped Jsx

/-- 与えられた関数 `fn` の `[0, 1]` 区間上での値のグラフ -/
def Plot (fn : Float → Float) (steps := 100) : Html :=
  -- `[0, 1)` 区間を `steps` 個に分割する
  let grids := Array.range steps
    |>.map (fun x => x.toFloat / steps.toFloat)

  -- データを JSON に変換
  let y := grids.map fn
  let jsonData : Array Json := grids.zip y
    |>.map (fun (x,y) => json% {x: $(toJson x), y: $(toJson y)});

  <LineChart width={400} height={400} data={jsonData}>
    <XAxis dataKey?="x" />
    <YAxis dataKey?="y" />
    <Line type={.monotone} dataKey="y" stroke="#8884d8" dot?={Bool.false} />
  </LineChart>

#html Plot (fun x => (x - 0.3) ^ 2 + 0.1)
#html Plot (fun x => 0.2 + 0.5 * Float.sin (7 * x))
