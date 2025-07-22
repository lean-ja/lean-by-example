/- # Problem 47
(Easy 🌟) Truth tables for logical expressions (part 2).
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
