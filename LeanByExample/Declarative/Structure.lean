/-
# structure
`structure` は構造体を定義するためのコマンドです。構造体とは、大雑把に説明すれば複数のデータをまとめて一つの型として扱えるようにしたものです。
-/

/-- 2次元空間の点 -/
structure Point (α : Type) : Type where
  x : α
  y : α

/- 構造体を定義すると、自動的に作られる関数があります。代表的なものは以下の２つです。

* フィールドにアクセスするための関数。
* コンストラクタ。

フィールドへのアクセサはフィールドの名前で、コンストラクタは `mk` という名前で作られます。
-/

-- アクセサ
#check (Point.x : {α : Type} → (Point α) → α)
#check (Point.y : {α : Type} → (Point α) → α)

def origin : Point Int := { x := 0, y := 0 }

/-- アクセサを使用する -/
example : Point.x origin = 0 := by rfl

-- コンストラクタ
#check (Point.mk : {α : Type} → α → α → Point α)

/- コンストラクタに `mk` 以外の名前を使いたい場合、`::` を使って次のようにします。-/
namespace Hidden --#

structure Prod (α : Type) (β : Type) where
  gen ::
  fst : α
  snd : β

-- コンストラクタの名前が gen になっている
#check Prod.gen

end Hidden --#
/- ## フィールド記法 { #FieldNotation }
構造体 `S` の項 `s : S` に `x` というフィールドがあるとき、`S.x s` の代わりに `s.x` と書くことができます。これにより、`s : S` におけるフィールド `x` の値を取得することができます。この関数適用を省略して「あたかもフィールドのように」値にアクセスする記法のことを **フィールド記法(field notation)** といいます。

Nim 言語や D 言語における [Uniform Function Call Syntax](https://ja.wikipedia.org/wiki/Uniform_Function_Call_Syntax) に似た仕様です。
-/

-- `.x` を付けるだけで値にアクセスできる
#guard origin.x = 0

/- 構造体のフィールドへのアクセスが典型的な使い方ですが、より一般の型に対してもフィールド記法は使用できます。

名前空間 `T` にある関数 `f` があって、項 `t : T` があったとします。このとき「`f` の `T` 型の非暗黙の引数のうち、最初のものに `x` を代入したもの」を `x.f` で表すことができます。-/

/-- 点が原点かどうか判定する。以下の２点に注意：
* 名前空間 `Point` の直下に定義されていること
* `Point α` 型の引数を持つこと
-/
def Point.isOrigin (p : Point Int) : Bool :=
  p.x = 0 && p.y = 0

-- フィールド記法が使える！
#guard origin.isOrigin

/- ## 項を定義する様々な構文
構造体の項を定義したい場合、複数の方法があります。波括弧記法が好まれますが、フィールド名が明らかな状況であれば[無名コンストラクタ](#{root}/Parser/AnonymousConstructor.md)を使用することもあります。-/

-- コンストラクタを使う
def sample0 : Point Int := Point.mk 1 2

-- 波括弧記法を使う
def sample1 : Point Int := { x := 1, y := 2 }

-- 無名コンストラクタを使う
def sample2 : Point Int := ⟨1, 2⟩

-- `where` を使う
def sample : Point Int where
  x := 1
  y := 2

/- ## 値の部分的変更
既存の構造体のフィールドの一部だけを変更した新しい構造体の項を作ることができます。
-/
section --#
variable {α : Type} [Add α]

/-- `p : Point` の x 座標を 2 倍にする -/
def Point.doubleX (p : Point α) : Point α :=
  { p with x := p.x + p.x}

#check Point.doubleX origin

end --#

/- ## 継承
既存の構造体に新しいフィールドを追加した新しい構造体を定義することができます。多重継承(複数の親を持つ構造体を作ること)も行うことができます。
-/

structure Point3D (α : Type) extends Point α where
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure ColorPoint3D (α : Type) extends Point α, RGBValue where
  z : α

/- ## 舞台裏

構造体は、コンストラクタが一つしかない帰納型であると見なすことができます。

### 帰納型による模倣

`structure` コマンドを使って定義した上記の `Point` を、`inductive` コマンドで模倣してみましょう。まず `mk` という単一のコンストラクタだけを持つ帰納型を定義します。このコンストラクタの各引数がフィールドに相当します。 -/

inductive Point' (α : Type) : Type where
  | mk (x y : α)

/- アクセサ関数が自動的に作られませんが、自分で作ることができます。-/

-- アクセサ関数が利用できない
#guard_msgs (drop warning) in --#
#check_failure Point'.x

/-- 自前で定義した `Point'` へのフィールドへのアクセサ -/
def Point'.x {α : Type} (p : Point' α) : α :=
  match p with
  | Point'.mk x _ => x

-- アクセサ関数が使えるようになった
#eval
  let p := Point'.mk 1 2
  p.x

/- 波括弧記法は `structure` コマンドで定義された型でなければ使用できないようです。 -/

-- 波括弧記法は使用できない
/--
warning: invalid {...} notation, structure type expected
  Point' Int
-/
#guard_msgs in
  #check_failure { x := 1, y := 2 : Point' Int}

/- ### 用途
この `structure` コマンドの代わりに `inductive` コマンドを用いる方法は、定義しようとしている構造体が命題をパラメータに持っているときに必要になります。[`Prop` の Large Elimination が許可されていない](#{root}/Type/Prop.md#NoLargeElim)ことにより、この場合はアクセサ関数が生成できないので `structure` コマンドが使用できず、エラーになります。 -/

-- `w` はデータなので、アクセサ関数が生成できなくてエラーになる
/-- error: failed to generate projections for 'Prop' structure, field 'w' is not a proof -/
#guard_msgs in
  structure Exists'.{v} {α : Sort v} (p : α → Prop) : Prop where
    intro ::

    w : α
    h : p w
