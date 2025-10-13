import LeanByExample.Modifier.Private.Lib
import Batteries.Tactic.OpenPrivate 

section
  -- 最初はアクセスできない
  #check_failure Point.private_sub

  -- `open private` コマンドを使用する
  open private Point.private_sub from LeanByExample.Modifier.Private.Lib

  -- アクセスできるようになった
  #check Point.private_sub
end
