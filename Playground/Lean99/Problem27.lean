/-
# 問題 27
(中級 🌟🌟) 集合の要素を互いに素な部分集合に分けるすべての方法をリストとして生成せよ。

すべての可能性を生成し、リストで返す関数を実装せよ。

> **注**: 元々は(a)(b)の2問だったが、(a)は(b)の特殊ケースなので省略。
-/
universe u
variable {α : Type}

namespace ListMonad

/-- monad instance of `List` -/
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

end ListMonad

open scoped ListMonad

def List.split (n : Nat) (xs : List α) : List (List α × List α) :=
  match n, xs with
  | 0, _ => [([], xs)]
  | _, [] => []
  | n + 1, x :: xs =>
    let ts := (xs.split n).map fun ⟨ys, zs⟩ => (x :: ys, zs)
    let ds := (xs.split (n + 1)).map fun ⟨ys, zs⟩ => (ys, x :: zs)
    ts ++ ds

#guard [1, 2].split 1 = [([1], [2]), ([2], [1])]

#guard [1, 2, 3].split 2 = [([1, 2], [3]), ([1, 3], [2]), ([2, 3], [1])]

#guard [1, 2, 3].split 3 = [([1, 2, 3], [])]

#guard [1, 2, 3].split 0 = [([], [1, 2, 3])]

def group (pattern : List Nat) (xs : List α): List <| List <| List α :=
  match pattern, xs with
  | [], _ => [[]]
  | n :: ns, xs => do
    let (g, rs) ← xs.split n
    let gs ← group ns rs
    pure <| g :: gs

#guard group [1, 2] [1, 2, 3] = [[[1], [2, 3]], [[2], [1, 3]], [[3], [1, 2]]]

#guard group [2, 1] [2, 4, 6] = [[[2, 4], [6]], [[2, 6], [4]], [[4, 6], [2]]]

#guard group [1, 1] [1, 2] = [[[1], [2]], [[2], [1]]]

-- The following codes are for test and you should not edit these.

/-- pattern of 2D `List` -/
def List.pattern (xs : List (List α)) : List Nat :=
  xs.map List.length

def Nat.factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * n.factorial

def runTest [ToString α] [BEq α] (pattern : List Nat) (xs : List α) : IO Unit := do
  if pattern.foldl (· + ·) 0 != xs.length then
    throw <| IO.userError s!"invalid test case: the sum of pattern should be equal to the length of the input list."

  let result := group pattern xs
  let pattern_check := result.map List.pattern
    |>.all (· = pattern)
  if not pattern_check then
    throw <| .userError s!"pattern check failed: some elements of result has invalid pattern."

  let distinct_check := result.eraseDups.length = result.length
  if not distinct_check then
    throw <| .userError s!"distinct check failed: the elements of result should be distinct."

  let expected_length := pattern.map Nat.factorial
    |>.foldl (· * ·) 1
    |> (fun x => xs.length.factorial / x)
  let length_check := result.length = expected_length
  if not length_check then
    throw <| .userError s!"length check failed: the length of result should be equal to {expected_length}."

  IO.println "OK!"

#eval runTest [1, 2, 3] <| List.range 6

#eval runTest [2, 2, 4] <| List.range 8

#eval runTest [2, 3, 4] <| List.range 9
