/-
# instance
`instance` は，型クラスのインスタンスを定義するための構文です．
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

/-
## 舞台裏
`instance` は `@[instance]` タグが付けられた `def` と同じように振る舞います．
-/

-- `List` 同士を足すことはできない
#check_failure [1] + [2]

-- インスタンスを宣言する
@[instance]
def instListAdd {α : Type} : Add (List α) where
  add := List.append

-- リスト同士を足すことができるようになった
-- 実装としては，上で指定した通り `List.append` が使われる
#check [1] + [2]

end Instance --#
