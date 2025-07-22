/- # Problem 48
(Easy 🌟) Truth tables for logical expressions (part 3).

Generalize Problem 47 in such a way that the logical expression may contain any number of logical variables. Define table/2 in a way that table(List,Expr) prints the truth table for the expression Expr, which contains the logical variables enumerated in List.
-/
universe u

namespace ListMonad

/-- monad instance of `List` -/
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
