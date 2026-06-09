/- # proof_wanted

`proof_wanted` はその名の通り、証明を公募するためのコマンドです。

`sorry` とよく似た機能を持つコマンドです。構文的には `theorem` に似ていますが、証明を書く必要がありません。証明を書かないで済むという点で `sorry` と同様です。
-/
import Batteries.Util.ProofWanted
set_option warn.sorry false --#

variable (n : Nat)

-- proof_wanted で証明を省略できる
proof_wanted result : n + 0 = n

-- sorry で同様のことができる
theorem another_result : n + 0 = n := by sorry
