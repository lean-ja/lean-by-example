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

structure MyProd (α : Type) (β : Type) where
  gen ::
  fst : α
  snd : β

-- コンストラクタの名前が gen になっている
#check MyProd.gen

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
#check_failure Point'.x

/-- 自前で定義した `Point'` へのフィールドへのアクセサ -/
def Point'.x {α : Type} (p : Point' α) : α :=
  match p with
  | Point'.mk x _ => x

-- アクセサ関数が使えるようになった
#eval
  let p := Point'.mk 1 2
  p.x

/- ### 用途
この `structure` コマンドの代わりに `inductive` コマンドを用いる方法は、定義しようとしている構造体が命題をパラメータに持っているときに必要になります。[`Prop` の Large Elimination が許可されていない](#{root}/Type/Prop.md#NoLargeElim)ことにより、この場合はアクセサ関数が生成できないので `structure` コマンドが使用できず、エラーになります。 -/

-- `w` はデータなので、アクセサ関数が生成できなくてエラーになる
/-⋆-//--
error: failed to generate projection `MyExists.w` for the 'Prop'-valued type `MyExists`, field must be a proof, but it has type
  α
-/
#guard_msgs in --#
structure MyExists.{v} {α : Sort v} (p : α → Prop) : Prop where
  intro ::

  w : α
  h : p w
