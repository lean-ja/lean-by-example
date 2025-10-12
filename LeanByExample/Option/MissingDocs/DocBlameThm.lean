import Lean

open Lean Elab Command Name

/--
ドキュメントコメントが付与されていない定理に対して警告を発するリンター。
デフォルトでは有効。
-/
register_option linter.docBlameThm : Bool := {
  defValue := true
  descr := "docBlameThmリンターを有効にする"
}

/--
ある位置 `pos` 以降にソースコード内で登場するすべての宣言名を収集する
-/
private def getNamesFrom (pos : String.Pos) : CommandElabM (Array Syntax) := do
  let drs := declRangeExt.toPersistentEnvExtension.getState (asyncMode := .local) (← getEnv)
  let fm ← getFileMap
  let mut nms := #[]
  for (nm, rgs) in drs do
    if pos ≤ fm.ofPosition rgs.range.pos then
      let ofPos1 := fm.ofPosition rgs.selectionRange.pos
      let ofPos2 := fm.ofPosition rgs.selectionRange.endPos
      nms := nms.push (mkIdentFrom (.ofRange ⟨ofPos1, ofPos2⟩) nm)
  return nms

/-- ドキュメントコメントが付与されているかどうか判定する -/
def Lean.Name.hasDocString (c : Name) (env : Environment) : CoreM Bool := do
  let doc? ← findDocString? env c
  return doc?.isSome

/-- ある宣言が `theorem` で宣言されているかどうか判定する -/
def Lean.Name.isTheorem (c : Name) : CommandElabM Bool := do
  let info ← getConstInfo c
  match info with
  | .thmInfo _ => return true
  | _  => return false

@[inherit_doc linter.docBlameThm]
def docBlameThmLinter : Linter where
  run := withSetOptionIn fun stx ↦ do
    -- リンターが有効になっていなければ何もしない
    unless Linter.getLinterValue linter.docBlameThm (← Linter.getLinterOptions) do
      return

    -- どこかにエラーがあれば何もしない
    if (← get).messages.hasErrors then
      return

    -- ユーザが定義した名前を取得する
    let names := (← getNamesFrom (stx.getPos?.getD default))
      |>.filter (! ·.getId.isInternal)

    let env ← getEnv
    for constStx in names do
      let constName := constStx.getId
      -- 定理でなければ無視する
      if ! (← constName.isTheorem) then
        continue
      -- ドキュメントコメントがなければ警告を出す
      let hasDocStr ← liftCoreM <| constName.hasDocString  env
      if ! hasDocStr then
        Linter.logLint linter.docBlameThm constStx
          m!"`{constName}`にドキュメントコメントを与えてください。"

initialize addLinter docBlameThmLinter
