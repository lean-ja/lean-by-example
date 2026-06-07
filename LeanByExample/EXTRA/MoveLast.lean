variable [BEq α] [Inhabited α]

def Array.moveLast (xs : Array α) (x : α) : Array α :=
  xs.filter (· != x) ++ xs.filter (· == x)

#guard Array.moveLast #[1, 2, 0, 3, 4, 0, 5] 0 == #[1, 2, 3, 4, 5, 0, 0]

def Array.moveLastInPlace (xs : Array α) (x : α) : Array α := Id.run do
  let n := xs.size
  let mut ys : Vector α n := xs.toVector
  let mut write := 0

  -- x でない要素を順序を保ったまま前に詰める
  for hi : i in [0:n] do
    if ys[i] != x then
      ys := ys.set! write ys[i]
      write := write + 1

  -- 残りを x で埋める
  for hi : i in [write:n] do
    ys := ys.set i x

  return ys.toArray

#eval Array.moveLastInPlace #[1, 2, 0, 3, 4, 0, 5] 0
