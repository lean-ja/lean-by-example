import Lake

/-!
This script generates the import list for a directory of Lean files.
* Almost all of this script is taken from <https://github.com/lurk-lab/yatima/blob/main/lakefile.lean>.
* <https://github.com/lurk-lab/yatima> is licensed under the MIT license.
-/

open Lake DSL System

partial def getLeanFilePaths (fp : FilePath) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    (← fp.readDir).foldlM (fun acc dir => getLeanFilePaths dir.path acc) acc
  else
    return if fp.extension == some "lean" then acc.push fp else acc

open Lean (RBTree)

def getAllFiles (dirName : String) : IO $ List String := do
  let paths := (← getLeanFilePaths ⟨dirName⟩).map toString
  let paths : RBTree String compare := RBTree.ofList paths.toList -- ordering
  return paths.toList

def getImportsString (dirName : String) : IO String := do
    let paths ← getAllFiles dirName
    if paths.isEmpty then
      throw $ IO.userError "no files found"
    let imports := paths.map $ fun p =>
        p.replace FilePath.pathSeparator.toString "."
          |> (String.replace · ".lean" "")
          |> ("import " ++ ·)
    return s!"{"\n".intercalate imports}\n"

def main (args : List String) : IO UInt32 := do
  if args.length != 2 then
    throw $ IO.userError "usage: lake exe importAll <dirName> <mode>"
  let dirName := args[0]!
  let fileName := dirName ++ ".lean"
  let mode := args[1]!

  -- write mode
  if mode == "write" then
    IO.FS.writeFile ⟨fileName⟩ (← getImportsString dirName)
    return 0

  -- check mode: mainly for CI
  else if mode == "check" then
    let importsFromUser ← IO.FS.readFile ⟨fileName⟩
    let expectedImports ← getImportsString dirName
    if importsFromUser != expectedImports then
      IO.eprintln s!"Invalid import list in {fileName}"
      IO.eprintln "Try running 'lake exe importAll <dirName> write'"
      return 1
    return 0

  else
    throw $ IO.userError "mode must be 'write' or 'check'"
