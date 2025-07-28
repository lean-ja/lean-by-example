/- 整数配列 `nums` が与えられたとき、すべての `0` を配列の末尾に移動させてください。ただし、**0 以外の要素の相対的な順序は維持**する必要があります。

なお、この操作は**配列をコピーせずに、その場（in-place）で行う**必要があります。
-/
variable {α : Type} [BEq α]

/-- 配列`arr`の要素`a`が与えられたときに、
他の要素の位置関係を維持したまま、すべての`a`を配列の末尾に移動させる

ただし、すべての操作を in-place で行う必要がある。
**TODO**: この関数が in-place であることをどうやって確認できるか？
-/
def Array.move (arr : Array α) (a : α) : Array α := Id.run do
  let mut arr := arr
  let mut write := 0
  -- まず `a` 以外の要素を前詰めで配置
  for x in arr do
    if x != a then
      arr := arr.set! write x
      write := write + 1
  -- 残りの部分を `a` で埋める
  for i in [write:arr.size] do
    arr := arr.set! i a
  return arr

#eval show IO Unit from do
  let mut arr := #[1, 0, 2, 0, 3]
  arr := dbgTraceIfShared "!" arr
  arr := Array.pop arr
  IO.println <| ptrAddrUnsafe arr
  arr := Array.pop arr
  IO.println <| ptrAddrUnsafe arr

#guard Array.move #[1, 0, 2, 0, 3] 0 == #[1, 2, 3, 0, 0] -- `0` を末尾に移動
#guard Array.move #[1, 2, 3] 0 == #[1, 2, 3] -- `0` がないので変化なし
#guard Array.move #[] 0 == #[] -- 空配列はそのまま
#guard Array.move #[0, 0, 0] 0 == #[0, 0, 0] -- `0` しかないので変化なし
#guard Array.move #[1, 2, 3, 4] 5 == #[1, 2, 3, 4] -- `5` がないので変化なし
