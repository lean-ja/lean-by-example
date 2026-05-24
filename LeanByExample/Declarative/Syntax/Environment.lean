-- # Environment.lean ファイル

import LeanByExample.Declarative.Syntax.Syntax
import Lean

open Lean

/-- import先のファイル名 -/
private def fileName : Name := `LeanByExample.Declarative.Syntax.Syntax

/-- `Arith`のための構文とマクロの定義が終わった直後の状態の`Environment` -/
initialize env_of_arith_stx : Environment ← do
  -- コンパイル時にLeanにoleanファイルを見つけさせるために必要
  initSearchPath (← findSysroot)

  -- importModulesの前で初期化を許可する必要がある
  unsafe Lean.enableInitializersExecution

  importModules #[{module := fileName}] {} (loadExts := true)
