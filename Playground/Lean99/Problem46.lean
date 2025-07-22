/- # Problem 46
(Intermediate 🌟🌟) Truth tables for logical expressions.
-/


def table (p : Bool → Bool → Bool) : List (List Bool) :=
  [
    [true, true, p true true],
    [true, false, p true false],
    [false, true, p false true],
    [false, false, p false false]
  ]

#guard table (fun a b => And a (Or a b)) ==
  [
    [true, true, true],
    [true, false, true],
    [false, true, false],
    [false, false, false]
  ]
