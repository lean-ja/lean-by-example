import Plausible

namespace Foldr
  /- ## foldr で書ける関数たち

  ### 和の計算
  -/

  variable {α β : Type}

  /-- 和の計算 -/
  def sum [Zero α] [Add α] (xs : List α) : α :=
    match xs with
    | [] => 0
    | x :: xs => x + sum xs

  -- インスタンス暗黙引数を使うことはできない(未実装)
  #guard_msgs (drop error) in
    #test ∀{α : Type}[Zero α][Add α](xs : List α), sum xs = xs.foldr (· + ·) 0

  example [Zero α] [Add α] (xs : List α) : sum xs = xs.foldr (· + ·) 0 := by
    -- 単に rfl としても失敗する
    fail_if_success rfl

    -- simp では示すことができない
    fail_if_success simp_all [sum, List.foldr]

    delta sum List.foldr
    rfl

end Foldr

namespace Foldr
  /- ### List の長さの計算 -/

  /-- Listの長さ -/
  def length {α : Type} (xs : List α) : Nat :=
    match xs with
    | [] => 0
    | _ :: xs => 1 + length xs

  -- length も foldr で書くことができる！
  example {α : Type} (xs : List α) : length xs = xs.foldr (fun _ n => 1 + n) 0 := by
    delta length List.foldr
    rfl

  /- ### List を逆にする -/

  /-- Listを逆にする -/
  def reverse {α : Type} (xs : List α) : List α :=
    match xs with
    | [] => []
    | x :: xs => reverse xs ++ [x]

  -- reverse も foldr で書くことができる！
  example {α : Type} (xs : List α) : reverse xs = xs.foldr (fun x xs => xs ++ [x]) [] := by
    delta reverse List.foldr
    rfl

end Foldr
