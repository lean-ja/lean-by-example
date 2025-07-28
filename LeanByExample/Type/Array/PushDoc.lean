/-
> Adds an element to the end of an array. The resulting array's size is one greater than the input
array. If there are no other references to the array, then it is modified in-place.
>
> This takes amortized `O(1)` time because `Array α` is represented by a dynamic array.
-/
--#--
import LeanByExample.DocCmd
/--
info: Adds an element to the end of an array. The resulting array's size is one greater than the input
array. If there are no other references to the array, then it is modified in-place.

This takes amortized `O(1)` time because `Array α` is represented by a dynamic array.

Examples:
* `#[].push "apple" = #["apple"]`
* `#["apple"].push "orange" = #["apple", "orange"]`
-/
#guard_msgs in
#doc Array.push
--#--
