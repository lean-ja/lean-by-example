/-
# instance
`instance` は、型クラスのインスタンスを定義するためのコマンドです。
-/
namespace Instance --#

/-- 平面 -/
structure Point (α : Type) where
  x : α
  y : α

/-- 原点 -/
def origin : Point Int := { x := 0, y := 0 }

-- 数値のように足し算をすることはできない
#check_failure (origin + origin)

/-- 平面上の点の足し算ができるようにする -/
instance {α : Type} [Add α] : Add (Point α) where
  add p q := { x := p.x + q.x, y := p.y + q.y }

-- 足し算ができるようになった
#check (origin + origin)

/- ## インスタンスの連鎖
インスタンスは連鎖させることができます。言い換えると、「`a` が `C` のインスタンスならば、`f a` も `C` のインスタンスである」というようなインスタンス宣言ができます。Lean コンパイラは再帰的にインスタンスを探します。
-/

/-- 偶数 -/
inductive Even : Type where
  | zero : Even
  | succ : Even → Even
deriving DecidableEq

/-- 偶数から自然数への変換 -/
def Even.toNat : Even → Nat
  | zero => 0
  | succ n => 2 + (Even.toNat n)

/-- Even を文字列に変換することを可能にする。
同時に #eval も可能になる。-/
instance : ToString Even where
  toString := toString ∘ Even.toNat

/-- Even.zero を 0 と書けるようにする -/
instance : OfNat Even 0 where
  ofNat := Even.zero

-- 実際に Even.zero を 0 と書けるようになった
#guard (0 : Even) = Even.zero

/-- インスタンス連鎖を利用して OfNat を実装。
n について OfNat の実装があれば、n + 2 についても OfNat の実装を得る。-/
instance {n : Nat} [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := Even.succ (OfNat.ofNat n)

#guard (2 : Even) = Even.succ Even.zero

-- 奇数については OfNat の実装はない
#check_failure (3 : Even)

/- なお、インスタンス連鎖の回数には上限があります。-/

-- ギリギリセーフ
#eval (254 : Even)

-- 上限を超えてしまった
#check_failure (256 : Even)

/-
## 舞台裏
`instance` は `[instance]` 属性を付与された [`def`](./Def.md) と同じようにはたらきます。ただし `instance` はインスタンス名を省略することができるという違いがあります。
-/

-- `List` 同士を足すことはできない
#check_failure [1] + [2]

-- インスタンスを宣言する
@[instance]
def instListAdd {α : Type} : Add (List α) where
  add := List.append

-- リスト同士を足すことができるようになった
-- 実装としては、上で指定した通り `List.append` が使われる
#guard [1] + [2] = [1, 2]

-- インスタンスを削除する
attribute [-instance] instListAdd

-- リスト同士を足すことができなくなった
#check_failure [1] + [2]

end Instance --#
