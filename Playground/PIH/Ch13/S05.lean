import Playground.PIH.Ch13.S04

/- Alternative は選択を表す -/

instance : Alternative Parser where
  failure := fun _ => none

  -- 最初のパーサが成功するならそれを返し、そうでなければ後のパーサを試す
  orElse := fun p q input =>
    match p input with
    | some result => some result
    | none => q () input
