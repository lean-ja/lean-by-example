/-
# rename_i
`rename_i` は、`✝` がついてアクセス不能になった変数に名前を付けることができます。

一般に、`rename_i x₁ x₂ ... xₐ` により、最初の `a` 個のアクセス不能変数に名前を付けることができます。
-/

example {n : Nat} (h0 : n ≠ 0) : n ≥ 1 := by
  cases n

  case zero =>
    contradiction

  case succ _ =>
    -- `n✝` が infoview に表示される
    -- これは `succ` の引数に名前をつけなかったため

    -- 名前をつける
    rename_i n
    show Nat.succ n ≥ 1

    simp

/- 必要な変数をアクセス不能にしてしまうこと自体を避けるべきであるため、`rename_i` を使うべき場面は多くありませんが `remane_i` の使用によりコードが簡単になることがあります。-/

variable {m : Nat}

/-- 自然数が0でも1でも2でもなければ3以上.
`case` をネストさせて示した場合. -/
example (h0 : m ≠ 0) (h1 : m ≠ 1) (h2 : m ≠ 2) : 3 ≤ m := by
  cases m with
  | zero => contradiction
  | succ m =>
    cases m with
    | zero => contradiction
    | succ m =>
      cases m with
      | zero => contradiction
      | succ m =>
        show 3 ≤ m + 3
        simp

/-- 自然数が0でも1でも2でもなければ3以上.
`rename_i` を使って示した場合. -/
example (h0 : m ≠ 0) (h1 : m ≠ 1) (h2 : m ≠ 2) : 3 ≤ m := by
  -- 仮定から `m = 0, 1, 2` のときは考えなくていい
  repeat
    cases m
    contradiction
    rename_i m

  -- 自然数 `m` に対して `3 ≤ m + 3` を示せばよい
  clear h0 h1 h2
  show 3 ≤ m + 3

  -- これは明らか
  simp

/-- 補足。おそらく最も簡潔な証明。 -/
example (h0 : m ≠ 0) (h1 : m ≠ 1) (h2 : m ≠ 2) : 3 ≤ m := by
  let .succ m := m
  let .succ m := m
  let .succ m := m

  show 3 ≤ m + 3
  simp
