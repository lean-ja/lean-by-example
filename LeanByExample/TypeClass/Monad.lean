/- # Monad

`Monad` は、圏論におけるモナドという概念からその名がある型クラスで、大雑把に言えば逐次的な計算を表します。この型クラスを実装した型に対しては、do 構文と呼ばれる手続き型プログラミングを一般化したような構文が使用できるようになります。
-/

/- ## 典型的なインスタンス

### Id

`Id` 関手はモナドです。`Id` の場合、do 構文は単に手続き型プログラミングを模したものになります。
-/

private def eratosthenesAux (n : Nat) : Array Bool := Id.run do
  let mut isPrime := Array.replicate (n + 1) true

  isPrime := isPrime.set! 0 false
  isPrime := isPrime.set! 1 false

  for p in [2 : n + 1] do
    if not isPrime[p]! then
      continue

    if p ^ 2 > n then
      break

    let mut q := p * p
    while q <= n do
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

#guard (eratosthenes 100).size = 25

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
