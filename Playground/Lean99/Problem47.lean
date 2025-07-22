/-
# 問題 47
(初級 🌟) 論理式の真理値表（その2）を作成せよ。
-/

def table (p : Bool → Bool → Bool) : List (List Bool) :=
  [
    [true, true, p true true],
    [true, false, p true false],
    [false, true, p false true],
    [false, false, p false false]
  ]

#guard table (fun a b => a && (a || b)) ==
  [
    [true, true, true],
    [true, false, true],
    [false, true, false],
    [false, false, false]
  ]
