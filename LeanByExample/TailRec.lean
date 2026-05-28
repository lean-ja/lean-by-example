
def countNonTR (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => countNonTR n + 1

def countTR (n : Nat) : Nat :=
  countTRAux n 0
where
  countTRAux (n acc : Nat) : Nat :=
    match n, acc with
    | 0, acc => acc
    | n + 1, acc => countTRAux n (acc + 1)


def main (args : List String) : IO Unit := do
  let x := 10_0000
  match args with
  | [] =>
    throw <| IO.userError "引数が必要です: `nontr` または `tr` を指定してください"
  | "nontr" :: _ =>
    IO.println s!"countNonTR {x} = {countNonTR x}"
  | "tr" :: _ =>
    IO.println s!"countTR {x} = {countTR x}"
  | _ =>
    throw <| IO.userError "不明な引数です: `nontr`"
