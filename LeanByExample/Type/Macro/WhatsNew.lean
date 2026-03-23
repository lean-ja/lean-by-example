import Mathlib.Util.WhatsNew

-- `macro_rules` コマンドの `whatsnew` コマンドによる出力の中に、`Macro` 型の項が含まれている
/-- Macro -/
#guard_msgs (substring := true) in whatsnew in
  macro_rules
  | `(zeroLit) => `(1)
