/- # proof_wanted

`proof_wanted` はその名の通り、証明を公募するためのコマンドです。

`sorry` とよく似た機能を持つコマンドです。構文的には `theorem` に似ていますが、証明を書く必要がありません。証明を書かないで済むのは `sorry` と同様ですが、`proof_wanted` で証明された定理は後で参照することができないという違いがあります。
-/
import Batteries.Util.ProofWanted

variable (n : Nat)

-- proof_wanted で証明を省略できる
proof_wanted result : n + 0 = n

-- sorry で同様のことができる
#guard_msgs (drop warning) in --#
theorem another_result : n + 0 = n := by sorry

-- sorry で証明した定理は参照できるが
#check another_result

-- proof_wanted で宣言した定理は参照できない
#guard_msgs (drop warning) in --#
#check_failure result
