import Plausible --#
/- # Alternative

`Alternative` 関手は、回復可能な失敗を表現します。

## インスタンス
重要なインスタンスとして、`Option` は `Alternative` のインスタンスです。
-/
#synth Alternative Option

/- また [`List`](#{root}/Type/List.md) も `Alternative` のインスタンスにすることができます。 -/

-- モナドのインスタンスにする
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

-- Alternative のインスタンスにする
instance : Alternative List where
  failure := @List.nil
  orElse l l' := List.append l (l' ())

/- ## 構文
`Alternative` のインスタンスにすると、`<|>` という二項演算子が使えるようになります。
これは評価を順に行っていって、失敗したら単に次に進むということを繰り返しながら、成功するまで評価を続けます。
-/

#eval (some 2 <|> none <|> some 5) = some 2
#eval (none <|> none <|> some 5 <|> some 4) = some 5

/- 早期に成功した場合、後続の項は評価されません。 -/

/-⋆-//-- info: some "hello" -/
#guard_msgs in --#
#eval some "hello" <|> (dbg_trace "foo!"; some "world")

/- ## guard 関数

「条件 `p` が真ならば何もしない。そうでなければ失敗とする」という処理のために `guard` 関数が用意されています。
-/
section
  /- ## filter の再帰を使う定義と、使わない定義を比較する -/

  variable {α : Type}

  /-- do 構文による filter の実装 -/
  def List.doFilter (p : α → Bool) (xs : List α) : List α := do
    -- リスト `xs` から要素 `x` を取り出す
    let x ← xs

    -- `p x` が真なら残す
    guard <| p x

    return x

  -- 再帰を使う標準の定義と一致する
  #test
    ∀ {α : Type} (p : α → Bool) (xs : List α),
    List.doFilter p xs = List.filter p xs
end
