/- # sorry

証明の細部を埋める前にコンパイルが通るようにしたいとき，証明で埋めるべき箇所に `sorry` と書くとコンパイルが通るようになります．ただし，`sorry` を使用しているという旨の警告が出ます． -/

-- Fermat の最終定理
def FermatLastTheorem :=
  ∀ x y z n : Nat, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

theorem flt : FermatLastTheorem :=
  sorry
