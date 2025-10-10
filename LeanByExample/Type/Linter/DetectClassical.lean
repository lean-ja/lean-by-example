-- Linter/DetectClassical.lean の内容

import Lean

/--
`detectClassical` リンターは、`Classical.choice` 公理に依存する宣言に対して警告を発する。
デフォルト値は `true`
-/
register_option linter.detectClassical : Bool := {
  defValue := true
  descr := "detectClassicalリンターを有効にする"
}

open Lean Elab Command

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

@[inherit_doc linter.detectClassical]
def detectClassicalLinter : Linter where
  run := withSetOptionIn fun stx ↦ do
    -- リンターが有効になっていなければ何もしない
    unless Linter.getLinterValue linter.detectClassical (← Linter.getLinterOptions) do
      return

    -- どこかにエラーがあれば何もしない
    if (← get).messages.hasErrors then
      return

    -- ユーザが定義した名前を取得する
    let names := (← getNamesFrom (stx.getPos?.getD default))
      |>.filter (! ·.getId.isInternal)

    for constStx in names do
      let constName := constStx.getId
      let axioms ← collectAxioms constName

      -- 公理に依存していなければスルーする
      if axioms.isEmpty then
        return

      -- 選択原理に依存していれば警告を出す
      if axioms.contains `Classical.choice then
        Linter.logLint linter.detectClassical constStx
          m!"`{constName}` depends on `Classical.choice`.\nAll axioms: {axioms.toList}"

initialize addLinter detectClassicalLinter
