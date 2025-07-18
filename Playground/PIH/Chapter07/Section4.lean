/- ## 畳込関数 foldl -/

namespace Foldl
  variable {α : Type}

  /-- sum の末尾再帰バージョン -/
  def sum {α : Type} [Zero α] [Add α] (xs : List α) : α :=
    sum' 0 xs
  where
    sum' : α → List α → α
    | acc, [] => acc
    | acc, x :: xs => sum' (acc + x) xs

  -- sum は foldl で書くことができる！
  example [Zero α] [Add α] (xs : List α) : sum xs = xs.foldl (· + ·) 0 := by
    dsimp [sum]
    delta sum.sum' List.foldl
    rfl

end Foldl
