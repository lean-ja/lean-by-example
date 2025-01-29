/-
# class
`class` は **型クラス(type class)** を定義するためのコマンドです。型クラスを用いると、複数の型に対して定義され、型ごとに異なる実装を持つような関数を定義することができます。例えば「和を取る操作」のような、`Nat` や `Int` や `Rat` など複数の型に対して同じ名前で定義したい関数を作りたいとき、型クラスが適しています。
-/
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

型クラスが行っていることを `class` を使わずにDIYしてみると、型クラスの理解が深まるでしょう。`class` として上で定義したものを、もう一度 [構造体](./Structure.md)として定義してみます。-/

/-- 構造体でモノイドクラスを真似たもの -/
structure Monoid' (α : Type) where
  e : α
  op : α → α → α

/-- 自然数がモノイドのインスタンスであるという主張を再現したもの -/
def instMonoid'Nat : Monoid' Nat where
  e := 0
  op := Nat.add

/- このとき構造体 `Monoid'` のフィールド `Monoid'.e` は、「`Monoid'` の項に対して `α` の要素を返す」関数なので、次のような型を持ちます。-/

#check (Monoid'.e : {α : Type} → (self : Monoid' α) → α)

/- `self : Monoid' α` が暗黙の引数ではなく明示的な引数なので、型クラスのように書くことはできません。-/

#guard_msgs (drop warning) in --#
#check_failure (Monoid'.e : Nat)

/- しかし、インスタンスを引数として渡せば、型クラスのように `Nat` の要素を取り出すことができます。-/

#check (Monoid'.e instMonoid'Nat : Nat)

/- 構造体による模倣と本物の型クラスの違いがどこにあるのかおわかりいただけたでしょうか。最大の違いは、引数の `instMonoid'Nat` が省略できるかどうかです。

ここで(本物の)型クラスにおける単位元関数 `e` の型を調べてみると、`self : Monoid' α` が角括弧 `[ .. ]` で囲われていることがわかります。-/

#check (Monoid.e : {α : Type} → [_self : Monoid α] → α)

/- これは **インスタンス暗黙引数(instance implicit)** と呼ばれるもので、この場合 Lean に対して `Monoid' α` 型の項を自動的に合成するよう指示することを意味します。また、型クラスのインスタンス暗黙引数を自動的に合成する手続きのことを、 **型クラス解決(type class resolution)** と呼びます。-/

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
error: failed to synthesize
  Plus Nat (List Nat) (IO ?_)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
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
/- ## class inductive { #ClassInductive }
基本的に型クラスの下部構造は構造体ですが、一般の[帰納型](#{root}/Declarative/Inductive.md)を型クラスにすることも可能です。それには `class inductive` というコマンドを使います。
-/

/-- 全単射があるという同値関係 -/
structure Equiv (α : Type) (β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : invFun ∘ toFun = id
  right_inv : toFun ∘ invFun = id

@[inherit_doc] infixl:25 " ≃ " => Equiv

/-- その型の濃度を知っていることを意味する型クラス。
証明無関係の制約により、返り値の型を Prop にしてはいけない。-/
class inductive HasCardinal (X : Type) : Type where
  /-- 有限集合は濃度が計算できる -/
  | finite (n : Nat) (f : X ≃ Fin n)

  /-- 可算無限集合は濃度が計算できる -/
  | countable (f : X ≃ Nat)

/-- Bool の濃度は計算できる -/
instance : HasCardinal Bool := by
  apply HasCardinal.finite (n := 2)
  constructor

  -- Bool → Fin 2 を作る
  case toFun => exact (fun b => if b then 1 else 0)

  -- Fin 2 → Bool を作る
  case invFun => exact (fun ⟨x, _⟩ => x == 1)

  -- invFun ∘ toFun は Bool 上の恒等関数
  case left_inv =>
    ext b
    cases b <;> simp

  -- toFun ∘ invFun は Fin 2 上の恒等関数
  case right_inv =>
    ext ⟨x, h⟩
    simp only [Fin.isValue, Function.comp_apply, beq_iff_eq, id_eq]
    match x with
    | 0 => simp
    | 1 => simp

/-- 可算無限までしかない順序数もどき -/
inductive Ordinal : Type where
  | nat (n : Nat)
  | omega
deriving DecidableEq

def Ordinal.toString : Ordinal → String
  | Ordinal.nat n => ToString.toString n
  | Ordinal.omega => "ω"

instance : ToString Ordinal := ⟨Ordinal.toString⟩

/-- X の濃度が計算できる場合、X の濃度を返す関数 -/
def HasCardinal.card (X : Type) [h : HasCardinal X] : Ordinal :=
  match h with
  | finite n _ => Ordinal.nat n
  | countable _ => Ordinal.omega

-- 単に card という名前でアクセスできるようにする
export HasCardinal (card)

-- Bool の濃度が計算できた
#guard card Bool = Ordinal.nat 2
