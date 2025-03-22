/-
# instance
`instance` は、型クラスのインスタンスを定義するためのコマンドです。
-/

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
  | zero
  | succ (n : Even)
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

/- ## インスタンス優先度

Lean では、同じ型と型クラスの組に対して複数のインスタンスを定義することができます。たとえば、次のようにモノイドという型クラスを定義したとします。
-/

/-- モノイド -/
class Monoid (α : Type) where
  /-- 単位元 -/
  unit : α

  /-- 演算 -/
  op : α → α → α

  /-- 結合法則 -/
  assoc : ∀ x y z : α, op (op x y) z = op x (op y z)

/- このとき `Nat` という一つの型に対して、２つの `Monoid` のインスタンスを定義することができ、後から定義した方が優先されます。 -/
section
  /- ## 優先度を指定しないインスタンスを２つ重ねた例 -/

  local instance : Monoid Nat where
    unit := 0
    op x y := x + y
    assoc x y z := by ac_rfl

  local instance : Monoid Nat where
    unit := 1
    op x y := x * y
    assoc x y z := by ac_rfl

  -- 後から宣言した方が優先される
  #guard (Monoid.unit : Nat) = 1
end
/- しかし、`priority` 構文を使うとインスタンス優先度を設定することができます。たとえば、`priority := low` とするとインスタンス優先度が `low` に設定されて、優先されなくなります。 -/
section
  /- ## priority := low の使用例 -/

  local instance : Monoid Nat where
    unit := 0
    op x y := x + y
    assoc x y z := by ac_rfl

  local instance (priority := low) : Monoid Nat where
    unit := 1
    op x y := x * y
    assoc x y z := by ac_rfl

  -- 後から宣言した方が優先されなくなる！
  #guard (Monoid.unit : Nat) = 0
end
/- 逆に `priority := high` とするとインスタンス優先度が `high` に設定されて、優先されるようになります。 -/
section
  /- ## priority := high の使用例 -/

  local instance (priority := high) : Monoid Nat where
    unit := 0
    op x y := x + y
    assoc x y z := by ac_rfl

  local instance : Monoid Nat where
    unit := 1
    op x y := x * y
    assoc x y z := by ac_rfl

  -- 後から宣言した方が優先されなくなる！
  #guard (Monoid.unit : Nat) = 0
end
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
