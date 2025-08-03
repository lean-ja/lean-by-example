/- # Vector

`Vector` は、長さが固定された配列です。標準ライブラリにおいて、次のように定義されています。

{{#include ./Vector/Def.md}}

`Vector` の要素を定義するには、`#v[a₁, a₂, .. aₙ]` のように書きます。
-/

#check #v[1, 2, 3]

/- ## 用途

典型的な使用場面は、配列に対してその配列の長さが一定であることを保証したい場合です。

たとえば、配列の順番を逆にする関数を定義したいとします。「配列の要素を順に交換していくことで逆順にする」というアルゴリズムで実装してみます。
-/

/-- 配列を逆順にする関数。
インデックスアクセスの妥当性証明を `swapIfInBounds` を使うことで回避している。 -/
def Array.myReverse₁ {α : Type} (arr : Array α) : Array α := Id.run do
  let mut array := arr
  let size := array.size
  for i in [0 : size / 2] do
    array := array.swapIfInBounds i (size - 1 - i)
  return array

#guard Array.myReverse₁ #[1, 2, 3, 4, 5] = #[5, 4, 3, 2, 1]
#guard Array.myReverse₁ (#[] : Array Nat) = #[]

/- ここで `Array.swapIfInBounds` ではなくて `Array.swap` を使用すると、インデックスアクセスの妥当性の証明が必要になります。しかし、`let mut` で宣言した配列の長さは変わってしまう可能性があるので、この証明は困難です。
-/
set_option warn.sorry false in --#

def Array.myReverse₂ {α : Type} (arr : Array α) : Array α := Id.run do
  let mut array := arr

  -- `array` は可変な配列なので、
  -- `size = array.size` が常に成り立つとは限らない！
  let size := array.size

  for h : i in [0 : size / 2] do
    -- これは証明できる
    have : i < size := by
      dsimp [(· ∈ ·)] at h
      grind

    have : i < array.size := by
      -- `size = array.size` が成り立つことを Lean に伝える手段が難しくて
      -- 証明が回らない
      dsimp [(· ∈ ·)] at h
      fail_if_success grind
      sorry

    -- 同様に証明できない
    have : size - 1 - i < array.size := by
      dsimp [(· ∈ ·)] at h
      fail_if_success grind
      sorry

    array := array.swap i (size - 1 - i)
  return array

/- そこで `Array` の代わりに `Vector` を使用すると、配列の長さの情報が型レベルで固定されるので、Lean に「`for` によるループの間、配列のサイズが変わらない」ことを伝えることができ、インデックスアクセスの妥当性が容易に証明できるようになります。 -/

def Array.myReverse₃ {α : Type} (arr : Array α) : Array α := Id.run do
  -- 配列ではなくて可変なベクトルとして保持する
  -- 可変変数だろうと型は変えられないので、長さが変わらないことを Lean に伝えられる
  let mut vec := arr.toVector
  let size := vec.size
  for h : i in [0 : size / 2] do
    -- 証明が通るようになった！
    have : i < vec.size := by
      dsimp [(· ∈ ·)] at h
      grind
    have : size - 1 - i < vec.size := by grind
    vec := vec.swap i (size - 1 - i)

  -- ベクトルを配列に戻して返す
  return vec.toArray
