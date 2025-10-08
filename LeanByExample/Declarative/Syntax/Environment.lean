import LeanByExample.Declarative.Syntax.Syntax
import Lean

open Lean

/-- import先のファイル名 -/
private def fileName : Name := `LeanByExample.Declarative.Syntax.Syntax

/-- `Arith`のための構文とマクロの定義が終わった直後の状態の`Environment` -/
initialize env_of_arith_stx : Environment ← do
  initSearchPath (← findSysroot) -- コンパイル時にLeanにoleanファイルを見つけさせるために必要
  importModules #[{module := fileName}] {} (loadExts := true)
