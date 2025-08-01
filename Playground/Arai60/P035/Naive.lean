variable {α : Type} [BEq α] [Inhabited α] [Ord α]

instance : LE α := leOfOrd
instance : LT α := ltOfOrd

/-- ソートされた配列を受け取って、target の index を二分探索で探す -/
def binarySearch (nums : Array α) (target : α) : Option Nat := Id.run do
  let mut lower : Nat := 0  -- **TODO** 型指定が必要なのはどうして？
  let mut upper := nums.size - 1

  while lower ≤ upper do
    let mid := (upper + lower) / 2
    if nums[mid]! == target then
      return mid
    else if nums[mid]! < target then
      lower := mid + 1
    else if nums[mid]! > target then
      upper := mid - 1

  return none

#guard binarySearch #[1, 2, 3, 4, 5] 4 = some 3
#guard binarySearch #[1, 5, 7, 11, 14, 24, 26] 2 = none
#guard binarySearch #[1, 2, 3, 4, 5, 5, 6, 7] 4 = some 3
