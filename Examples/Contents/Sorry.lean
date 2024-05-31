/- # sorry

証明の細部を埋める前にコンパイルが通るようにしたいとき，証明で埋めるべき箇所に `sorry` と書くとコンパイルが通るようになります．ただし，`sorry` を使用しているという旨の警告が出ます． -/
import Batteries.Util.ProofWanted --#

-- Fermat の最終定理
def FermatLastTheorem :=
  ∀ x y z n : Nat, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

theorem flt : FermatLastTheorem :=
  sorry

/-! ## proof_wanted

`sorry` とよく似た機能を持つコマンドとして `proof_wanted` があります．
`proof_wanted` は構文的には `theorem` に似ていますが，証明を書く必要がありません．
証明を書かないで済むのは `sorry` と同様ですが，`proof_wanted` で宣言された定理は後で参照することができないという違いがあります．
-/

variable (n : Nat)

proof_wanted result : n + 0 = n

theorem another_result : n + 0 = n := by sorry

example : n + 0 = n := by
  -- `proof_wanted` で宣言した定理は証明なしでは使用できない
  fail_if_success rw [result]

  show n + 0 = n
  rw [another_result]
