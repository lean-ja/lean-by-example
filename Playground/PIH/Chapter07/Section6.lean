import Plausible
/- # 文字列の２進変換 -/

/-- ビット。0か1の数字 -/
abbrev Bit := Nat

/-- unfold関数 -/
def List.unfold {α β : Type} (f : β → Option (α × β)) (b : β) : List α :=
  helper f b []
where
  helper (f : β → Option (α × β)) (b : β) (acc : List α) : List α :=
    match f b with
    | none => acc
    | some (a, b) => helper f b (a :: acc)
  partial_fixpoint

#guard List.unfold (fun x => if x = 0 then none else some (x, x - 1)) 3 = [1, 2, 3]

/-- `f : α → α` を n 回繰り返し適用してリストを得る -/
def List.iterate {α : Type} (f : α → α) (a : α) (n : Nat) : List α :=
  match n with
  | 0 => []
  | n + 1 => a :: List.iterate f (f a) n

#guard List.iterate (· + 1) 0 5 = [0, 1, 2, 3, 4]
#guard List.iterate (· * 2) 1 4 = [1, 2, 4, 8]

namespace Play1

  /-- 2進数を10進数に変換する -/
  def bin2int (bs : List Bit) : Nat :=
    let weights := List.iterate (fun x => x * 2) 1 (bs.length)
    (List.zip weights bs)
      |>.map (fun (w, b) => w * b)
      |>.foldl (· + ·) 0

  #guard bin2int [1, 0, 1, 1] = 13

end Play1

namespace Play2
  /-- 2進数を10進数に変換する -/
  def bin2int (bs : List Bit) : Nat :=
    bs.foldr (fun a b => a + 2 * b) 0

  #guard bin2int [1, 0, 1, 1] = 13

end Play2

/-- サイズを8ビットに固定する -/
def make8 (bs : List Bit) : List Bit :=
  if bs.length ≤ 8 then
    bs ++ List.replicate (8 - bs.length) 0
  else
    bs.take 8

#guard make8 [1, 0, 1, 1] = [1, 0, 1, 1, 0, 0, 0, 0]

#test ∀ (xs : List Bit), (make8 xs).length = 8
