/-
# class
`class` は型クラスを定義するためのコマンドです。型クラスを用いると、複数の型に対して定義され、型ごとに異なる実装を持つような関数を定義することができます。例えば「和を取る操作」のような、`Nat` や `Int` や `Rat` など複数の型に対して同じ名前で定義したい関数を作りたいとき、型クラスが適しています。
-/
namespace Class --#
/-- 証明なしのバージョンのモノイド。
ただしモノイドとは、要素同士を「くっつける」操作ができて、
くっつけても変わらない要素があるようなもののこと。-/
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

/- ## 型クラス解決

型クラスが行っていることを `class` を使わずにDIYしてみると、型クラスの理解が深まるでしょう。`class` として上で定義したものを、もう一度 `structure` として定義してみます。-/

/-- 構造体でモノイドクラスを真似たもの -/
structure Monoid' (α : Type) where
  e : α
  op : α → α → α

/-- 自然数がモノイドのインスタンスであるという主張を再現したもの -/
def instMonoid'Nat : Monoid' Nat where
  e := 0
  op := Nat.add

/- このとき構造体 `Monoid'` のフィールド `Monoid'.e` は、「`Monoid'` の項に対して `α` の要素を返す」関数なので、次のような型を持ちます。-/

/-- info: Class.Monoid'.e {α : Type} (self : Monoid' α) : α -/
#guard_msgs in #check Monoid'.e

/- `self : Monoid' α` が暗黙の引数ではなく明示的な引数なので、型クラスのように書くことはできません。-/

#check_failure (Monoid'.e : Nat)

/- しかし、インスタンスを引数として渡せば、型クラスのように `Nat` の要素を取り出すことができます。-/

#check (Monoid'.e instMonoid'Nat : Nat)

/- 構造体による模倣と本物の型クラスの違いがどこにあるのかおわかりいただけたでしょうか。最大の違いは、引数の `instMonoid'Nat` が省略できるかどうかです。

ここで(本物の)型クラスにおける単位元関数 `e` の型を調べてみると、`self : Monoid' α` が角括弧 `[ .. ]` で囲われていることがわかります。-/

/-- info: Class.Monoid.e {α : Type} [self : Monoid α] : α -/
#guard_msgs in #check Monoid.e

/- これは**インスタンス暗黙引数**と呼ばれるもので、この場合 Lean に対して `Monoid' α` 型の項を自動的に合成するよう指示することを意味します。また、型クラスのインスタンス暗黙引数を自動的に合成する手続きのことを、**型クラス解決**と呼びます。-/

/- ## outParam
足し算を表現する型クラスを自分で定義してみましょう。名前は `Plus` としてみます。足し算は自然数の和 `Nat → Nat → Nat` のように、同じ型の中で完結する操作として定義されることが多いものですが、より一般的に `α → β → γ` で定義されるものとしてみます。
-/
namespace Bad --#
/-- 自前で定義した足し算記法のためのクラス -/
class Plus (α β γ : Type) where
  plus : α → β → γ

-- 足し算記法を定義
-- ライブラリにある足し算記号と被るのを避けるため変な記号にしておく
scoped infixl:65 " +ₚ " => Plus.plus

-- 自然数と自然数のリストとの足し算を定義
instance : Plus Nat (List Nat) (List Nat) where
  plus n ns := List.map (fun x => n + x) ns

-- 定義した記号が使えるようになった
#check 1 +ₚ [1, 2]

/- この定義は上手くいっているように見えますが、返り値の型である `γ` を指定しないと `#eval` で式の値が評価できないという問題があります。-/

-- メタ変数の番号を表示しない
set_option pp.mvars false

-- 返り値の型がわからないので型クラス解決ができないというエラーが出ている
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Plus Nat (List Nat) ?_
-/
#guard_msgs in #eval 1 +ₚ [1, 2]

-- 返り値の型を教えると評価できる
#eval (1 +ₚ [1, 2] : List Nat)

end Bad --#
/- ここで最初の `Plus` の定義を書き換え、返り値の型を `outParam` で修飾すると、上手くいくようになります。これは、`γ` が未知の状態でも型クラス解決を行うようになるためです。-/
namespace Good --#

-- `γ` の型 `Type` を `outParam` で包んで注釈する
class Plus (α β : Type) (γ : outParam Type) where
  plus : α → β → γ

scoped infixl:65 " +ₚ " => Plus.plus

instance : Plus Nat (List Nat) (List Nat) where
  plus n ns := List.map (fun x => n + x) ns

-- 返り値の型を教えなくても評価できるようになった！
#eval 1 +ₚ [1, 2]

end Good --#
end Class --#
