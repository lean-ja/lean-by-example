import Batteries.Data.MLList.Basic

/-- 遅延評価のリスト -/
abbrev LazyList := MLList Id

/-- リストのサイズ -/
def size := 100_000_000

/-- 適当な述語 -/
def P := fun n => n % 42 == 6

@[noinline]
def listTest (size : Nat) : Nat := Id.run do
  let llist := List.range size
  for l in llist do
    if P l then
      return l
  return 0

@[noinline]
def lazyListTest (size : Nat) : Nat := Id.run do
  let llist : MLList Id Nat := MLList.range |>.filter (fun n => n ≤ size)
  for l in llist do
    if P l then
      return l
  return 0

#time #eval listTest size
#time #eval lazyListTest size
