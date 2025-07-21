namespace Playground

variable {α : Type}

/-- リストを逆順にする関数。
`(· ++ ·)`を再帰的に使用しているのですごく効率が悪い実装になっている。 -/
@[grind]
def reverse (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs => reverse xs ++ [x]

#guard reverse [1, 2, 3] = [3, 2, 1]

/-- `reverse`関数をより汎用的にした関数 -/
@[grind]
def reverse' (xs ys : List α) : List α :=
  reverse xs ++ ys

-- **TODO** 右辺を`sorry`にすることで、「答えが分かっていない状態での等式変形による計算」を
-- シミュレートしてしている。しかし、もっとうまくやる方法があればもっとよい。
set_option warn.sorry false

/-- 基底部についての性質(計算) -/
@[grind]
theorem reverse'_nil (ys : List α) : reverse' [] ys = ys := by
  rw [reverse']
  dsimp [reverse]

/-- 再帰部についての性質(計算) -/
@[grind]
theorem reverse'_cons (x : α) (xs ys : List α) :
  reverse' (x :: xs) ys = reverse' xs ([x] ++ ys) := by
  rw [reverse']
  dsimp [reverse]
  ac_nf

/-- より効率の良い`reverse`の実装

**TODO** 末尾再帰にすることでより高速になっている例。
末尾再帰と言うよりは、`(· ++ ·)`を`::`で書き換えて高速化している例かもしれないが。
-/
@[grind]
def reverseAux (xs ys : List α) : List α :=
  match xs with
  | [] => ys
  | x :: xs => reverseAux xs (x :: ys)

@[csimp]
theorem reverseAux_eq_reverse' : @reverse' = @reverseAux := by
  funext α xs ys
  fun_induction reverseAux xs ys <;> grind

def fastReverse (xs : List α) : List α :=
  reverseAux xs []

end Playground
