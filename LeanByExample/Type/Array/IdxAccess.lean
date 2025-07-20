open IO

variable {α : Type} {valid : α → Nat → Prop}
variable [GetElem α Nat Nat valid] [GetElem? α Nat Nat valid]

/--
コレクション型に対して、そのインデックスアクセスの実行時間を計測する関数

* `col`: 対象となるコレクション
* `accessPoint`: 計算の中では、同じインデックスに対して何度もアクセスして平均時間を計測する。
  そこでアクセスするインデックス。
-/
@[noinline]
def evalIdxAccess (col : α) (accessPoint : Nat) : IO Nat := do
  -- アクセスを試みる回数
  let access_times := 1000

  -- コンパイラに最適化されて結果が変わることを防ぐために
  -- どうでもいい計算をする
  let mut sum := 0

  let mut sum_time := 0
  for _ in [0:access_times] do
    -- インデックスアクセスにかかる時間を測定する
    let start_time <- monoNanosNow
    let x := col[accessPoint]!
    let end_time <- monoNanosNow
    let time := end_time - start_time

    -- アクセス時間を合計する
    sum := (sum + x) % 2
    sum_time := sum_time + time

  IO.println s!"{sum} is computed..."
  return sum_time / access_times

def main : IO Unit := do
  let size := 10_000_000
  let accessPoint := size / 10
  let listTime ← evalIdxAccess (List.range size) accessPoint
  println s!"List access time: {listTime}"

  let arrayTime ← evalIdxAccess (Array.range size) accessPoint
  println s!"Array access time: {arrayTime}"

  if listTime < arrayTime then
    throw <| userError "List is faster than Array"

#eval main
