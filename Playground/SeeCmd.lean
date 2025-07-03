import Lean

open Lean

/-- 何もしないコマンド -/
elab "#see " id:ident : command => do
  -- `#see id`の`id`部分をクリックできるようにするために必要
  _ ← Elab.Command.liftCoreM <| Elab.realizeGlobalConstNoOverloadWithInfo id

  return ()
