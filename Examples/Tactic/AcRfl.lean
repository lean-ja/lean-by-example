/-
# ac_rfl
`ac_rfl` は，結合的(associative)かつ可換(commutative)な演算に対して，結合性と可換性だけから示せる等式を示すタクティクです．
-/

/-- 3次元格子点がなす空間 -/
@[ext]
structure Point : Type where
  x : Int
  y : Int
  z : Int

namespace Point

/-- `Point` 上の足し算 -/
def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/-- `Point` 上の足し算を `+` で表せるようにする -/
instance : Add Point where
  add := add

@[simp]
protected theorem x_add (a b : Point) : (a + b).x = a.x + b.x := rfl

@[simp]
protected theorem y_add (a b : Point) : (a + b).y = a.y + b.y := rfl

@[simp]
protected theorem z_add (a b : Point) : (a + b).z = a.z + b.z := rfl

/-- `Point` 上の足し算は可換 -/
protected theorem add_comm (a b : Point) : a + b = b + a := by
  ext
  all_goals
    simp
    apply Int.add_comm

/-- `Point` 上の足し算は結合的 -/
protected theorem add_assoc (a b c : Point) : a + b + c = a + (b + c) := by
  ext
  all_goals
    simp
    apply Int.add_assoc

-- `ac_rfl` から使えるように，`Std.Commutative` のインスタンスにする
instance : Std.Commutative (α := Point) (· + ·) where
  comm := Point.add_comm

-- `ac_rfl` から使えるように，`Std.Associative` のインスタンスにする
instance : Std.Associative (α := Point) (· + ·) where
  assoc := Point.add_assoc

-- 可換性と結合性から示せることなら示せる
example (a b c: Point) : (a + b) + c + (a + b) = a + a + b + b + c := by
  ac_rfl

/- `ac_rfl` は，上記の構造体 `Point` の例のように，自分で定義した演算が可換で結合的であることを後から簡単に利用できるようにしておきたいときに役立ちます．ここで `@[simp]` タグを付けるのは，可換性や結合法則は項の簡約ではないため上手くいかないということに注意してください．-/
