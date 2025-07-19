/- # Monad

`Monad` は、圏論におけるモナドという概念からその名がある型クラスで、大雑把に言えば逐次的な計算を表します。この型クラスを実装した型に対しては、do 構文と呼ばれる手続き型プログラミングを一般化したような構文が使用できるようになります。
-/

/- ## 典型的なインスタンス

### Id

`Id` 関手はモナドです。`Id` の場合、do 構文は単に手続き型プログラミングを模したものになります。
-/

/-- `n`以下の素数のリストを `Array Bool` の形で返す。
`i` 番目が `true` ならば `i` は素数で、`false` ならば合成数。 -/
def eratosthenesAux (n : Nat) : Array Bool := Id.run do
  let mut isPrime := Array.replicate (n + 1) true

  isPrime := isPrime.set! 0 false
  isPrime := isPrime.set! 1 false

  for p in [2 : n + 1] do
    if not isPrime[p]! then
      continue

    if p ^ 2 > n then
      break

    -- `p` の倍数を消していく
    let mut q := p * p
    while q ≤ n do
      isPrime := isPrime.set! q false
      q := q + p

  return isPrime

/-- エラトステネスの篩 -/
def eratosthenes (n : Nat) : Array Nat :=
  eratosthenesAux n
  |>.zipIdx
  |>.filterMap fun ⟨isPrime, i⟩ =>
    if isPrime then some i else none

#guard eratosthenes 10 = #[2, 3, 5, 7]

#guard
  let actual := eratosthenes 100
  let expected := #[
    2, 3, 5, 7, 11,
    13, 17, 19, 23, 29,
    31, 37, 41, 43, 47,
    53, 59, 61, 67, 71,
    73, 79, 83, 89, 97
  ]
  expected == actual

/- ### Option

[`Option`](#{root}/Type/Option.md) 関手はモナドです。`Option` の場合、do 構文によって「先行する計算のどれか一つでも `none` だったら `none` を返す。全部が `some` だったときだけ先へ進む」という処理を簡単に書けるようになります。

たとえば、配列の１つめの２つめと３つめの要素をまとめて取り出す関数を do 構文なしで書こうとすると次のようになり、インデックスアクセスがネストしてややこしくなります。
-/
namespace WithoutDo --#

def fstSndThird? (a : Array Nat) : Option (Nat × Nat × Nat) :=
  match a[0]? with
  | none => none
  | some x =>
    match a[1]? with
    | none => none
    | some y =>
      match a[2]? with
      | none => none
      | some z => some (x, y, z)

#guard fstSndThird? #[1] = none
#guard fstSndThird? #[1, 2] = none
#guard fstSndThird? #[1, 2, 3] = some (1, 2, 3)

end WithoutDo --#
/- しかし do 構文を使用すると、ネストを消し去ることができます。 -/
namespace Do --#

def fstSndThird? (a : Array Nat) : Option (Nat × Nat × Nat) := do
  let x ← a[0]?
  let y ← a[1]?
  let z ← a[2]?
  return (x, y, z)

#guard fstSndThird? #[1] = none
#guard fstSndThird? #[1, 2] = none
#guard fstSndThird? #[1, 2, 3] = some (1, 2, 3)

end Do --#

/- ### List

[`List`](#{root}/Type/List.md) 関手もモナドにすることができます。`List` の場合、do 構文を使用することで、リスト内包表記のような操作を簡潔に記述できます。

たとえば、2つのリストの直積を計算する関数は次のように書けます。 -/

/-- `List` をモナドインスタンスにする -/
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

def cartesianProduct (xs : List Nat) (ys : List Nat) : List (Nat × Nat) := do
  let x ← xs
  let y ← ys
  return (x, y)

#guard cartesianProduct [1, 2] [3, 4] = [(1, 3), (1, 4), (2, 3), (2, 4)]

/- ## インスタンス自作例

パーサーをモナドとして実装することができます。[^parser]
-/

/-- パーサ

* 返り値が `Option` で包まれているのは、パースが成功するとは限らないため
* 返り値の `α × String` は、`α` がパース結果、`String` が残りの入力文字列を表す
-/
def Parser (α : Type) := String → Option (α × String)

/-- `Parser`の`Functor.map`メソッドの実装

* パーサが成功すれば結果に関数を適用する
* 失敗したら失敗を伝搬する
-/
protected def Parser.map {α β : Type} (f : α → β) (p : Parser α) : Parser β :=
  fun input =>
    match p input with
    | none => none
    | some (a, rest) => some (f a, rest)

instance : Functor Parser where
  map := Parser.map

/-- `Parser`の`Applicative.pure`メソッドの実装 -/
protected def Parser.pure {α : Type} (x : α) : Parser α :=
  fun input => some (x, input)

/-- `Parser`の`Applicative.seq`メソッドの実装

関数を返すパーサ`pg`を、引数を返すパーサ`px ()`に適用して、
「その関数を引数に適用した結果を返すパーサ」を返す
-/
protected def Parser.seq {α β : Type} (pg : Parser (α → β)) (px : Unit → Parser α) : Parser β :=
  fun input =>
    match pg input with
    | none => none
    | some (g, out) => (g <$> px ()) out

instance : Applicative Parser where
  pure := Parser.pure
  seq := Parser.seq

instance : Monad Parser where
  bind := fun {_α _β} p f input =>
    match p input with
    | none => none
    | some (v, out) => f v out

/-
これでパーサを組み合わせるのに do 構文が利用できるようになります。
-/

/-- 基礎的なパーサ

入力文字が空の時は失敗し、それ以外の時は最初の文字を消費して返す
-/
def Parser.item : Parser Char := fun input =>
  match input with
  | ⟨[]⟩ => none
  | ⟨x :: xs⟩ => some (x, ⟨xs⟩)

/-- 3文字の文字列にマッチするパーサー -/
def Parser.three : Parser String := do
  let x ← item
  let y ← item
  let z ← item
  return String.mk [x, y, z]

#guard Parser.three "abcdef" = some ("abc", "def")

/-
[^parser]: モナドを利用するパーサの詳細については「Monadic Parser Combinators」と「Monadic parsing in Haskell」という論文を参照してください。
-/
