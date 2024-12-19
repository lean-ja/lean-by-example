/-
# ac_rfl
`ac_rfl` は、結合的(associative)かつ可換(commutative)な演算に対して、結合性と可換性だけから示せる等式を示すタクティクです。
-/

/-- 3次元格子点がなす空間 -/
@[ext]
structure Point : Type where
  x : Int
  y : Int
  z : Int

namespace Point --#

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

-- `ac_rfl` から使えるように、`Std.Commutative` のインスタンスにする
instance : Std.Commutative (α := Point) (· + ·) where
  comm := Point.add_comm

-- `ac_rfl` から使えるように、`Std.Associative` のインスタンスにする
instance : Std.Associative (α := Point) (· + ·) where
  assoc := Point.add_assoc

-- 可換性と結合性から示せることなら示せる
example (a b c: Point) : (a + b) + c + (a + b) = a + a + b + b + c := by
  ac_rfl

end Point --#

/- `ac_rfl` は、上記の構造体 `Point` の例のように、自分で定義した演算が可換で結合的であることを後から簡単に利用できるようにしておきたいときに役立ちます。ここで `@[simp]` タグを付けるのは、可換性や結合法則は項の単純化ではないため上手くいかないということに注意してください。-/

/- ## よくあるエラー
`ac_rfl` は、可換性と結合性の両方がインスタンスとして登録されていないと使えないことがあります。以下は、可換性だけが登録されているときに、可換性だけで示せそうな命題が示せないという例です。
-/

@[ext]
structure Color : Type where
  r : Nat
  g : Nat
  b : Nat

namespace Color --#
section

def add (a b : Color) : Color :=
  ⟨a.r + b.r, a.g + b.g, a.b + b.b⟩

instance : Add Color where
  add := add

/-- `add` は可換 -/
protected theorem add_comm (a b : Color) : a + b = b + a := by
  ext <;> apply Nat.add_comm

/-- `add_comm` を `Std.Commutative` に登録する。
local に宣言したので、このセクション内限定 -/
local instance : Std.Commutative (α := Color) (· + ·) where
  comm := Color.add_comm

example (a b : Color) : a + b = b + a := by
  -- ac_rfl がエラーになってしまう
  fail_if_success ac_rfl

  ext <;> apply Nat.add_comm

end
/- ## 結合法則と ac_rfl
上記のように、`ac_rfl` は可換性だけで示せることを可換性だけで示せないのですが、往々にして結合法則だけで示せることは結合法則だけで示すことができます。
-/
section

/-- `Color` の足し算は結合的 -/
protected theorem add_assoc (a b c : Color) : a + b + c = a + (b + c) := by
  ext <;> apply Nat.add_assoc

-- エラーになっているので、
-- Commutative のインスタンスはないことが確認できる
/--
error: failed to synthesize
  Std.Commutative fun x1 x2 => x1 + x2
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
  #synth Std.Commutative (α := Color) (· + ·)

/-- `add_comm` を `Std.Associative` に登録する。
local にしたのでセクション内でのみ有効 -/
local instance : Std.Associative (α := Color) (· + ·) where
  assoc := Color.add_assoc

-- 結合法則だけで示せることは示すことができる
example {a b c : Color} : (a + b) + (c + (b + a)) = a + b + c + b + a := by
  ac_rfl

end
end Color --#
