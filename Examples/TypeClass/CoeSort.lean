/-
# CoeSort
`CorSort` は [`Coe`](./Coe.md) と同じく型強制を定義するための型クラスですが，項ではなく型に対して適用されるところが違います．

たとえば，モノイドという数学的対象をどう形式化するか考えてみましょう．モノイドとは，集合 `M` とその上の二項演算 `* : M → M → M` であって，結合律を満たし，単位元を持つものです．インフォーマルには，「くっつける」演算が定義されている集合と考えても良いでしょう．たとえば自然数は加法に対してモノイドですし，文字列は連結に対してモノイドです．

ここでは以下のように形式化します．[^monoid]
-/
namespace CoeSort --#

structure Monoid where
  /-- 台集合 -/
  Carrier : Type

  /-- 単位元 -/
  neutral : Carrier

  /-- 二項演算 -/
  op : Carrier → Carrier → Carrier

/- 自然数やリストがモノイドであることを，上記の定義に基づいて形式化すると次のようになります．-/

def natAddMonoid : Monoid :=
  {
    Carrier := Nat,
    neutral := 0,
    op := (· + ·)
  }

def listMonoid (α : Type) : Monoid :=
  {
    Carrier := List α,
    neutral := [],
    op := (· ++ ·)
  }

/- ここでこの2つのモノイドの間の関数として，リストの長さを与える関数を考えてみます．-/

def length {α : Type} (xs : (listMonoid α).Carrier) : (natAddMonoid).Carrier :=
  List.length xs

/- 型アノテーションの中で `Carrier` が繰り返し現れています．上記でモノイドを「集合と演算の組」として定義したため，モノイドを集合とみなすことができないためです．毎回 `Carrier` を補うのは面倒に感じますね．`CoeSort` を使えば，このようなルーティンな型変換を自動で行うことができます．-/

instance : CoeSort Monoid Type where
  coe m := m.Carrier

-- 単に `listMonoid α` と書いただけで，`Carrier` への変換が暗黙的に行われる
def length' {α : Type} (xs : listMonoid α) : natAddMonoid :=
  List.length xs

/- [^monoid]: ここで紹介するモノイドの定義は `CoeSort` の紹介のために最低限必要な部分だけを取り出したもので，正確ではありません．上記の定義では二項演算が結合的であること，単位元が本当に単位元として振る舞うことが保証されません．また，そもそもモノイドは型クラスとして実装するべきです．そうすれば，自然数やリストにモノイドの構造を入れるために毎回新しい型を導入する必要はありません．-/

end CoeSort --#
