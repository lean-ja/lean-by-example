/-
現在のファイル名を出力する term elaborator
-/
import Lean.Elab.Command

open Lean Elab Term

def basename (path : String) : String :=
  (path.splitToList fun c => c == '/' || c == '\\').getLastD path

elab "this_file%" : term => do
  return Lean.mkStrLit (basename (← getFileName))

#guard this_file% == "ThisFile.lean"
