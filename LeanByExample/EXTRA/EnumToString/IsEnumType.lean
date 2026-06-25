import Lean

open Lean Meta

-- Bool は列挙型
run_meta
  let actual ← isEnumType ``Bool
  assert! actual

-- Nat は列挙型ではない
run_meta
  let actual ← isEnumType ``Nat
  assert! !actual
