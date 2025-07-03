import Lean

/- # \#see コマンド

何もしないコマンド。

`MyNat`や`MyList`のように標準にあるものを自前で作っているとき、標準ライブラリやMathlibにある定義・定理を参照できるようにメモしておく目的で主に使う。
-/

open Lean

/-- 何もしないコマンド -/
elab "#see " id:ident : command => do
  -- `#see id`の`id`部分をクリックできるようにするために必要
  _ ← Elab.Command.liftCoreM <| Elab.realizeGlobalConstNoOverloadWithInfo id

  return ()
