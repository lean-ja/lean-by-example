def addTwoNumbers : List Nat → List Nat → List Nat
  | [], [] => []
  | l1, l2 => addHelper l1 l2 0
where
  addHelper : List Nat → List Nat → Nat → List Nat
    | [], [], 0 => []
    | [], [], carry => [carry]
    | x::xs, [], carry =>
        let sum := x + carry
        (sum % 10) :: addHelper xs [] (sum / 10)
    | [], y::ys, carry =>
        let sum := y + carry
        (sum % 10) :: addHelper [] ys (sum / 10)
    | x::xs, y::ys, carry =>
        let sum := x + y + carry
        (sum % 10) :: addHelper xs ys (sum / 10)

#guard addTwoNumbers [2,4,3] [5,6,4] = [7,0,8]
#guard addTwoNumbers [9,9,9,9,9,9,9] [9,9,9,9] = [8,9,9,9,0,0,0,1]
