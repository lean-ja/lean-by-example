import Lean.Util.CollectAxioms
import Mathlib.Tactic.DeclarationNames

/--
「detectClassical」リンターは、`Classical.choice` 公理に依存する宣言に対して警告を発する。
-/
register_option linter.detectClassical : Bool := {
  defValue := true
  descr := "detectClassicalリンターを有効にする"
}

namespace DetectClassical

  open Lean Elab Command Mathlib.Linter

  @[inherit_doc linter.detectClassical]
  def detectClassicalLinter : Linter where run := withSetOptionIn fun stx ↦ do
    -- リンターが有効になっていなければ何もしない
    unless Linter.getLinterValue linter.detectClassical (← getOptions) do
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
          m!"'{constName}' depends on 'Classical.choice'.\n\nAll axioms: {axioms.toList}\n"

  initialize addLinter detectClassicalLinter

end DetectClassical
