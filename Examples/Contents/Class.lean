/-
# class
`class` は型クラスを定義するための構文です．型クラスを用いると，複数の型に対して定義され，型ごとに異なる実装を持つような関数を定義することができます．例えば「和を取る操作」のような，`Nat` や `Int` や `Rat` など複数の型に対して同じ名前で定義したい関数を作りたいとき，型クラスが適しています．
-/

/-- 証明なしのバージョンのモノイド -/
class Monoid (α : Type) where
  /-- 単位元 -/
  e : α

  /-- 二項演算 -/
  op : α → α → α

/-- 自然数はモノイド -/
instance : Monoid Nat where
  -- ゼロを単位元とする
  e := 0

  -- 加算を二項演算とする
  op := Nat.add

/-- 連結リストはモノイド -/
instance {α : Type} : Monoid (List α) where
  -- 空リストを単位元とする
  e := []

  -- リストの連結を二項演算とする
  op := List.append

-- `Nat` に対してモノイドの演算が使える
#guard Monoid.op 0 0 = 0

-- `List Nat` に対してモノイドの演算が使える
#guard Monoid.op [1] [2, 3] = [1, 2, 3]

-- `Nat` に対して単位元を取得する関数が使える
#guard (Monoid.e : Nat) = 0

-- `List Int` に対しても単位元を取得する関数が使える
#guard (Monoid.e : List Int) = []

/- ## 舞台裏

### 構造体による型クラスの模倣
型クラスが行っていることを `class` を使わずにDIYしてみると，型クラスの理解が深まるでしょう．`class` として上で定義したものを，もう一度 `structure` として定義してみます．-/

/-- 構造体でモノイドクラスを真似たもの -/
structure Monoid' (α : Type) where
  e : α
  op : α → α → α

/-- 自然数がモノイドのインスタンスであるという主張を再現したもの -/
def instMonoid'Nat : Monoid' Nat where
  e := 0
  op := Nat.add

/- このとき構造体 `Monoid'` のフィールド `Monoid'.e` は，「`Monoid'` の項に対して `α` の要素を返す」関数なので，次のような型を持ちます．-/

/-- info: Monoid'.e {α : Type} (self : Monoid' α) : α -/
#guard_msgs in --#
#check Monoid'.e

/- `self : Monoid' α` が暗黙の引数ではなく明示的な引数なので, 型クラスのように書くことはできません．-/

#check_failure (Monoid'.e : Nat)

/- しかし，インスタンスを引数として渡せば，型クラスのように `Nat` の要素を取り出すことができます．-/

#check (Monoid'.e instMonoid'Nat : Nat)

/- 構造体による模倣と本物の型クラスの違いがどこにあるのかおわかりいただけたでしょうか．最大の違いは，引数の `instMonoid'Nat` が省略できるかどうかです．-/

/- ### インスタンス暗黙引数と型クラス解決
ここで(本物の)型クラスにおける単位元関数 `e` の型を調べてみると, `self : Monoid' α` が角括弧 `[ .. ]` で囲われていることがわかります．-/

/-- info: Monoid.e {α : Type} [self : Monoid α] : α -/
#guard_msgs in --#
#check Monoid.e

/- これは**インスタンス暗黙引数**と呼ばれるもので，この場合 Lean に対して `Monoid' α` 型の項を自動的に合成するよう指示することを意味します．また，型クラスのインスタンス暗黙引数を自動的に合成する手続きのことを，**型クラス解決**と呼びます．-/
