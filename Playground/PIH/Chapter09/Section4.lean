import Playground.PIH.Chapter09.Section3

/-- 与えられたリストの部分リストを全て返す -/
def List.subs {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    let xss := subs xs
    xss ++ xss.map (x :: ·)

#guard [1].subs = [[], [1]]
#guard [1, 2].subs = [[], [2], [1], [1, 2]]
#guard [1, 2, 3].subs.length = 8

/-- リストに与えられた要素を挿入してできるリストを全て返す -/
def List.interleave {α : Type} : α → List α → List (List α)
  | x, [] => [[x]]
  | x, y :: ys =>
    (x :: y :: ys) :: (List.interleave x ys).map (y :: ·)

#guard [1, 2].interleave 3 = [[3, 1, 2], [1, 3, 2], [1, 2, 3]]

/-- 与えられたリストの要素の順列を全て返す -/
def List.perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    let rest := perms xs
    rest.map (List.interleave x ·) |>.flatten

#guard [1, 2].perms = [[1, 2], [2, 1]]
#guard [1, 2, 3].perms.length = 6
#guard [1, 2, 3, 4].perms.length = 24

/-- 与えられたリストの要素の取り出し方（順番の違いを区別する）をすべて返す -/
def List.choices {α : Type} : List α → List (List α) :=
  List.flatten ∘ List.map List.perms ∘ List.subs

#guard [1, 2].choices = [[], [2], [1], [1, 2], [2, 1]]
#guard [1, 2, 3].choices.length = 16
