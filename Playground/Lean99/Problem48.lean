/-
# 問題 48
(初級 🌟) 論理式の真理値表（その3）。

問題47を一般化し、論理式が任意個の論理変数を含む場合にも対応せよ。table(List,Expr) で、Listで列挙された論理変数を含む式Exprの真理値表を出力するようにせよ。
-/
universe u

namespace ListMonad

/-- List型のモナドインスタンス -/
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

end ListMonad

open scoped ListMonad

def Arity : (n : Nat) → Type
  | 0 => Bool
  | n + 1 => Bool → Arity n

def tablen (n : Nat) (p : Arity n) : List (List Bool) :=
  match n with
  | 0 => [[p]]
  | n + 1 => do
    let b ← [true, false]
    let result ← tablen n (p b) |>.map (b :: ·)
    return result

#guard tablen 1 (fun a => a) = [[true, true], [false, false]]

#guard tablen 2 (fun a b => a && b) = [
  [true, true, true],
  [true, false, false],
  [false, true, false],
  [false, false, false]
]

#guard tablen 2 (fun a b => !a || b) = [
  [true, true, true],
  [true, false, false],
  [false, true, true],
  [false, false, true]
]

#guard tablen 3 (fun a b c => a && b && c) = [
  [true, true, true, true],
  [true, true, false, false],
  [true, false, true, false],
  [true, false, false, false],
  [false, true, true, false],
  [false, true, false, false],
  [false, false, true, false],
  [false, false, false, false]
]
