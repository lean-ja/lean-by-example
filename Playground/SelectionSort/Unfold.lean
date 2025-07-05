import Plausible
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Nat.Basic

universe u v

variable {α : Type u} {β : Type v}

/-- 関数 `f : β → Option (α × β)` が none を返すまで繰り返し適用して、
結果を集めてリストを作る。 -/
def List.unfold (f : β → Option (α × β)) (b : β) : List α :=
  aux f b [] |> reverse
where
  aux (f : β → Option (α × β)) (b : β) (acc : List α) : List α :=
    match f b with
    | none => acc
    | some (a, b) => aux f b (a :: acc)
  partial_fixpoint

-- 初期値3から始めてカウントダウンする
#guard List.unfold (fun x => if x = 0 then none else some (x, x - 1)) 3 = [3, 2, 1]

section SelectionSort
  /- ## List.unfold を使用した選択ソートの実装 -/

  variable {α : Type}

  /-- 選択ソートのループ部分。リスト `l` の最小要素 `x : α` と、
  `l` から `x` を除いた残りの部分 `xs` を組にして返す。 -/
  def separateMin [LinearOrder α] (l : List α) : Option (α × List α) :=
    match l with
    | [] => none
    | _ => do
      let x ← List.min? l
      let xs := List.erase l x
      return (x, xs)

  /-- 選択ソート -/
  def List.selectionSort [LinearOrder α] : List α → List α :=
    List.unfold separateMin

  #guard [3, 1, 4, 1, 5, 9].selectionSort = [1, 1, 3, 4, 5, 9]

  -- 実際にソートになっていそう
  #test ∀ (l : List Nat), l.selectionSort = l.mergeSort

end SelectionSort
