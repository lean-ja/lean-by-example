/- # universe

`universe` は、宇宙レベルを表す変数を宣言するコマンドです。`universe u` と宣言すると、そのスコープ内で `u` を宇宙変数として使えるようになります。
-/

universe u

#check (Type u)

/-
ここで **宇宙(universe)** とは、項が再び型であるような型のことです。たとえば `Nat` や `Bool` は型ですが、Lean ではそのような型も項として扱われ、`Type` という型を持ちます。
-/

#check (Nat : Type)
#check (Bool : Type)

/- `Type` 自身も型ですが、`Type : Type` ではなく `Type : Type 1` です。`Type 1` の型は `Type 2` です。以下、`Type 2` の型は `Type 3` 等と無限に続きます。-/

#check (Type : Type 1)
#check (Type 1 : Type 2)
#check (Type 2 : Type 3)

/- 一般に `Type u` の型は `Type (u + 1)` になります。 -/

#check (Type u : Type (u + 1))

/- ## 宇宙多相

宇宙変数 `u` を明示的に宣言することによって、定義を **宇宙多相(universe polymorphic)** にすることができます。複数の型宇宙で同じように動作する定義が得られるということです。`Type u` を使えば [`Type`](#{root}/Type/Type.md) 上で宇宙多相にできますし、`Sort u` を使えば [`Prop`](#{root}/Type/Prop.md) も含めることができます。

### 例: Size 型クラス

たとえば、`size` という関数を提供する以下のような[型クラス](#{root}/Declarative/Class.md)を考えてみます。[^size]
-/
namespace Step0 --#

class Size (A : Type u) where
  size : A → Nat

export Size (size)

end Step0 --#
/- 配列やリストなどのコレクションの大きさを取得する統一的な手段を提供する型クラスというイメージです。 -/
namespace Step0 --#

instance : Size (List A) where
  size l := l.length

instance : Size (Array A) where
  size a := a.size

#guard size [1, 2, 3] = 3
#guard size #["a", "b", "c"] = 3

end Step0 --#
/-
この `size` 関数を型に対しても適用できるようにしたいと思ったとします。`size Bool = 2` や `size Unit = 1` といった具合にです。

この場合最も直接的な実装は `Type` に対して `Size` のインスタンスを定義することですが、任意の `A : Type` に対してそのサイズを計算することは不可能であるため、この方法では実装できません。
-/
namespace Step0 --#
set_option warn.sorry false in --#

instance : Size (Type u) where
  size A := sorry -- 実装を与える方法がない

end Step0 --#
/-
`Size` の実装を与える型を選択できるようにしなければいけないので、`size` 関数の引数となる型を `Size` の定義に含めるように書き直します。
-/
namespace Step1 --#

/-- 書き直した Size 型クラス -/
class Size {A : Type u} (a : A) where
  size : Nat

export Size (size)

instance (l : List A) : Size l where
  size := l.length

instance (a : Array A) : Size a where
  size := a.size

#guard size [1, 2, 3] = 3
#guard size #["a", "b", "c"] = 3

end Step1 --#
/-
このようにすると、`size` 関数を型に対しても定義できるようになります。
-/
namespace Step1 --#

instance : Size Bool where
  size := 2

instance : Size Unit where
  size := 1

#guard size Bool = 2
#guard size Unit = 1

end Step1 --#
/-
上記の `Size` 型クラスの定義では、宇宙多相であることが必要です。実際に推論された宇宙レベルを表示してみると、異なる宇宙レベルが使用されていることがわかります。`.{u}` と表示されている部分が宇宙レベルを表しています。
-/
namespace Step1 --#

-- 推論された宇宙レベルを表示する
set_option pp.universes true

/-- info: size.{1} Bool : Nat -/
#guard_msgs in --#
#check size Bool

/-- info: size.{0} (List.cons.{0} 1 List.nil.{0}) : Nat -/
#guard_msgs in --#
#check size [1]

end Step1 --#
/-
### 例: *.rec

Lean の標準ライブラリにある例でいうなら、帰納型を定義したときに自動生成される `*.rec` という関数も宇宙多相です。定義を見ると、`.{u}` と書かれており宇宙多相であることがわかります。
-/

/--
info: Nat.rec.{u} {motive : Nat → Sort u} (zero : motive Nat.zero) (succ : (n : Nat) → motive n → motive n.succ) (t : Nat) :
  motive t
-/
#guard_msgs in --#
#check Nat.rec

/-
単に宇宙多相であるだけでなく、この関数は宇宙多相であることが必要な例になっています。

以下のように、`u = 0` とすれば `Sort 0 = Prop` なので証明に使うことができます。
-/

theorem Nat.add_zero' (n : Nat) : n + 0 = n :=
  Nat.rec
    (motive := fun (n : Nat) => n + 0 = n)
    (by simp)
    (fun n ih => by simp)
    n

/- そして、`u = 1` とすれば `Sort 1 = Type` なのでデータを扱う普通の関数が定義できます。 -/

/-- 階乗関数 -/
def Nat.factorial (n : Nat) : Nat :=
  Nat.rec
    (motive := fun (_ : Nat) => Nat)
    1
    (fun n ih => (n + 1) * ih)
    n

#guard Nat.factorial 5 = 120

/-
[^size]: この `Size` 型クラスを実装して宇宙多相にする例は、[Scientific Computing in Lean](https://lecopivo.github.io/scientific-computing-lean/)の TypeClasses as Interfaces and Function Overloading という章で紹介されている例をそのまま使用しています。
-/
