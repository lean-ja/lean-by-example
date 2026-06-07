variable [BEq α] [Inhabited α]

def Array.moveLast (xs : Array α) (x : α) : Array α :=
  xs.filter (· != x) ++ xs.filter (· == x)

def Array.moveLastInPlace (xs : Array α) (x : α) : Array α := Id.run do
  let n := xs.size
  let mut ys : Vector α n := xs.toVector
  let mut write := 0

  for hi : i in [0:n] do
    if ys[i] != x then
      ys := ys.set! write ys[i]
      write := write + 1

  for hi : i in [write:n] do
    ys := ys.set i x

  return ys.toArray

inductive Algorithm where
  | inPlace
  | normal

def Algorithm.label : Algorithm -> String
  | .inPlace => "moveLastInPlace"
  | .normal => "moveLast"

def mkInput (n : Nat) : Array Nat := Id.run do
  let mut xs := Array.emptyWithCapacity n
  for i in [0:n] do
    let v := if i % 10 == 0 then 0 else i + 1
    xs := xs.push v
  return xs

def fingerprint (xs : Array Nat) : Nat :=
  xs.size + xs[0]! + xs[xs.size - 1]!

def elapsedMs (start stop : Nat) : Nat :=
  (stop - start) / 1000000

def runAlgorithm (alg : Algorithm) (xs : Array Nat) : Nat :=
  let ys :=
    match alg with
    | .inPlace => Array.moveLastInPlace xs 0
    | .normal => Array.moveLast xs 0
  fingerprint ys

def benchOne (alg : Algorithm) (name : String) (n : Nat) : IO Nat := do
  let xs <- IO.lazyPure fun _ => mkInput n
  let start <- IO.monoNanosNow
  let fp <- IO.lazyPure fun _ => runAlgorithm alg xs
  let stop <- IO.monoNanosNow
  let ns := stop - start
  IO.println s!"{name}: {elapsedMs start stop} ms, fingerprint={fp}"
  return ns

partial def repeatBench (alg : Algorithm) (n : Nat) (runs : Nat) : IO (Array Nat) := do
  let rec loop (i : Nat) (acc : Array Nat) : IO (Array Nat) := do
    if i == runs then
      return acc
    else
      let ns <- benchOne alg s!"{alg.label}[{i}]" n
      loop (i + 1) (acc.push ns)
  loop 0 #[]

def nsToMsString (ns : Nat) : String :=
  let ms := ns / 1000000
  let frac := (ns % 1000000) / 1000
  s!"{ms}.{frac} ms"

def main : IO Unit := do
  let n := 10000000
  let runs := 3
  IO.println s!"n={n}, target frequency=10%, runs={runs}"
  discard <| benchOne .inPlace "warmup moveLastInPlace" 100000
  discard <| benchOne .normal "warmup moveLast" 100000
  let inPlace <- repeatBench .inPlace n runs
  let normal <- repeatBench .normal n runs
  let inPlaceAvg := inPlace.foldl (· + ·) 0 / runs
  let normalAvg := normal.foldl (· + ·) 0 / runs
  IO.println s!"avg moveLastInPlace={nsToMsString inPlaceAvg}"
  IO.println s!"avg moveLast={nsToMsString normalAvg}"
  IO.println s!"speedup={(normalAvg * 100) / inPlaceAvg}% of in-place time"
