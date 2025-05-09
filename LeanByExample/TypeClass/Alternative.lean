import Plausible --#
/- # Alternative

`Alternative` [関手](#{root}/TypeClass/Functor.md)は、回復可能な失敗を表現します。あるいは、選択的な計算を表すと表現することもできます。
-/
/- ## 定義

`Alternative` クラスは、`Applicative` 型クラスを継承して概ね次のように定義されています。
-/
namespace Hidden --#

universe u v --#

class Alternative (f : Type u → Type v) extends Applicative f where
  /--
  空のコレクションまたは回復可能な失敗を生成する。
  -/
  failure : {α : Type u} → f α
  /--
  `Alternative`インスタンスに応じて、値を拾ったり最初に成功した結果を返すことで
  `failure`から回復したりする。
  -/
  orElse : {α : Type u} → f α → (Unit → f α) → f α

end Hidden --#
/- ## 構文
`Alternative` のインスタンスにすると、`<|>` という二項演算子が使えるようになります。`<|>` は `orElse` とほぼ対応していますが、少し型が異なります。
-/
section
  variable {α : Type}

  -- `F` は `Alternative` 関手
  variable {F : Type → Type} [Alternative F]

  -- `orElse` と `<|>` は基本的には同じもの
  example (a : F α) (b : Unit → F α) : Alternative.orElse a b = (a <|> b ()) := rfl

  -- 型が少し `orElse` と異なる
  example : F α → F α → F α := fun x y => (x <|> y)

end
/- ## インスタンス

### Option
重要なインスタンスとして、[`Option`](#{root}/Type/Option.md) は `Alternative` のインスタンスです。`failure` は `none` として実装されていて、`(· <|> ·)` は最初の `none` でない値を選択するような処理として実装されています。-/

#guard (failure : Option Nat) = none

#guard (some 2 <|> none <|> some 5) = some 2

#guard (none <|> none <|> some 5 <|> some 4) = some 5

/- `Option` の `(· <|> ·)` は評価を順に行っていって、失敗したら単に次に進むということを繰り返しながら、成功するまで評価を続けます。早期に成功した場合、後続の項は評価されません。 -/

/-⋆-//-- info: some "hello" -/
#guard_msgs in --#
#eval some "hello" <|> (dbg_trace "foo!"; some "world")

/-
### List
[`List`](#{root}/Type/List.md) も `Alternative` のインスタンスにすることができます。 -/

-- モナドのインスタンスにする
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

-- Alternative のインスタンスにする
instance : Alternative List where
  failure := @List.nil
  orElse l l' := List.append l (l' ())

#guard ([] <|> [1, 2, 3]) = [1, 2, 3]

#guard ([1, 2, 3] <|> [4, 5, 6]) = [1, 2, 3, 4, 5, 6]

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
