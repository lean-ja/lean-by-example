import Lake
open Lake DSL

package examples {
  -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60autoImplicit.20true.60.20is.20evil/near/355145527
  moreLeanArgs := #["-DrelaxedAutoImplicit=false"]
  moreServerArgs := #["-DrelaxedAutoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "b6ec7450650a5945bf4244751be4a5cf1fee962f"

@[default_target]
lean_lib Examples {
  -- add lib config here
}

/-!
`import` 文を自動生成するスクリプト
`lake run import_all` で実行できる
<https://github.com/lurk-lab/yatima/tree/main> からコードの大部分を拝借した
-/
section ImportAll

  partial def getLeanFilePaths (fp : FilePath) (acc : Array FilePath := #[]) :
      IO $ Array FilePath := do
    if ← fp.isDir then
      (← fp.readDir).foldlM (fun acc dir => getLeanFilePaths dir.path acc) acc
    else return if fp.extension == some "lean" then acc.push fp else acc

  open Lean (RBTree)

  def getAllFiles : ScriptM $ List String := do
    let paths := (← getLeanFilePaths ⟨"Examples"⟩).map toString
    let paths : RBTree String compare := RBTree.ofList paths.toList -- ordering
    return paths.toList

  def getImportsString : ScriptM String := do
    let paths ← getAllFiles
    let imports := paths.map fun p =>
      "import " ++ ((p.splitOn ".").head!.replace "/" ".").replace "\\" "."
    return s!"{"\n".intercalate imports}\n"

  script import_all do
    IO.FS.writeFile ⟨"Examples.lean"⟩ (← getImportsString)
    return 0

  script import_all? do
    let importsFromUser ← IO.FS.readFile ⟨"Examples.lean"⟩
    let expectedImports ← getImportsString
    if importsFromUser != expectedImports then
      IO.eprintln "Invalid import list in 'Examples.lean'"
      IO.eprintln "Try running 'lake run import_all'"
      return 1
    return 0

end ImportAll
