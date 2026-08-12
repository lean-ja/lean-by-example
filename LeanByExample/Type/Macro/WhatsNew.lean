import Mathlib.Util.WhatsNew

-- `macro_rules` コマンドの `#whats_new` コマンドによる出力の中に、`Macro` 型の項が含まれている
/-- Macro -/
#guard_msgs (substring := true) in
  #whats_new in
    macro_rules
    | `(zeroLit) => `(1)
