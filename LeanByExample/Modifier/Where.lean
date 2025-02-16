/- # where
`where` 句(where clause)を使うと、定義をする前に変数を使用することができます。主に、ヘルパー関数を宣言するために使用されます。
-/

/-- 自然数 `n` の素因数とその重複度のリストを返す -/
partial def primeFactorsMult (n : Nat) : List (Nat × Nat) :=
  loop 2 n [] |>.reverse
where
  /-- 自然数 `d` に対して、`n` の重複度 `μ` と `d` のペア `(d, μ)` を返す。-/
  extract (d n : Nat) : Nat × Nat :=
    if d ≤ 1 then
      (1, 0)
    else if n % d != 0 then
      (d, 0)
    else
      let (d, m) := extract d (n / d)
      (d, m + 1)

  /-- ヘルパー関数 -/
  loop (d target : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    if target ≤ 1 then
      acc
    else
      let (d, m) := extract d target
      if m = 0 then
        loop (d + 1) target acc
      else
        loop (d + 1) (target / (d ^ m)) ((d, m) :: acc)
