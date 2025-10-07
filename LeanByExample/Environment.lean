import LeanByExample.Syntax
import Lean

open Lean

initialize environment : Environment ← importModules #[{module := `LeanByExample.Syntax}] {} (loadExts := true)
