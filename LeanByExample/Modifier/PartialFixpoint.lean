/- # partial_fixpoint

`partial_fixpoint` は、Leanが自動的に停止性を証明できない関数の宣言に対して、「停止すると証明する」「停止するという証明を放棄する」以外の選択肢を提供します。
-/
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
/- ## partial との違い

[`partial`](#{root}/Modifier/Partial.md) と比較すると、`partial_fixpoint` で定義された関数は簡約が通ります。以下の例では、`partial` と指定された関数は [`#reduce`](#{root}/Modifier/Reduce.md) コマンドで一切簡約されないのに対して、`partial_fixpoint` と指定された関数は多少簡約されています。
-/

/-- 何もつけずに定義した階乗もどき関数 -/
def factorial (x : Nat) : Option Nat :=
  match x with
  | 0 => some 1
  | x + 1 => do
    let y ← factorial x
    return (x + 1) * y

-- 簡約で評価結果が得られる
/-⋆-//-- info: some 120 -/
#guard_msgs in --#
#reduce factorial 5

/-- partial と指定した階乗もどき関数 -/
partial def partialFactorial (x : Nat) : Option Nat :=
  match x with
  | 0 => some 1
  | x + 1 => do
    let y ← partialFactorial x
    return (x + 1) * y

-- 一切簡約されない
/-⋆-//-- info: partialFactorial 5 -/
#guard_msgs in --#
#reduce partialFactorial 5

/-- partial_fixpoint と指定した階乗もどき関数 -/
def fixpointFactorial (x : Nat) : Option Nat :=
  match x with
  | 0 => some 1
  | x + 1 => do
    let y ← fixpointFactorial x
    return (x + 1) * y
partial_fixpoint

/-⋆-//-- info: Decidable.rec (fun h => none) (fun h => (Classical.choice ⋯).1) (Classical.choice ⋯) -/
#guard_msgs in --#
#reduce fixpointFactorial 5
