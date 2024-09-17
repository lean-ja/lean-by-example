/- # simps

補題を [`simp`](../../Tactic/Simp.md) で使えるようにするのは `[simp]` 属性を付与することで可能ですが、`[simps]` 属性(または `@[simps]` タグ)を利用すると `simp` で使用するための補題を自動的に生成してくれます。

例えば、ユーザが `Point` という構造体を定義し、`Point` 上の足し算を定義したところを考えましょう。このとき、足し算はフィールドの値の足し算で定義されているため、「`Point` の和の `x` 座標」は `x` 座標の和ですが、これはそのままでは `simp` で示すことができません。`[simps]` 属性を `Point.add` 関数に付与することで、`simp` で示せるようになります。
-/
import Mathlib.Tactic.Simps.Basic -- simps 属性を使うため

@[ext]
structure Point where
  x : Int
  y : Int

/-- Point の和 -/
def Point.add (p q : Point) : Point :=
  { x := p.x + q.x, y := p.y + q.y }

/-- 和の x 座標は x 座標の和 -/
example (a b : Point) : (Point.add a b).x = a.x + b.x := by
  -- この状態だと `simp` で示せない
  fail_if_success simp

  rfl

-- `Point.add` に `[simps]` 属性を付与する
attribute [simps] Point.add

example (a b : Point) : (Point.add a b).x = a.x + b.x := by
  -- simp 補題が自動的に生成されて、simp で示せるようになった
  simp

/- 上記の例では `attribute` コマンドで属性を付与していますが、タグも使用できます。-/

@[simps]
def Point.sub (p q : Point) : Point :=
  { x := p.x - q.x, y := p.y - q.y }

example (a b : Point) : (Point.sub a b).x = a.x - b.x := by simp

/- `@[simps?]` に換えると、生成された補題を確認することができます。-/

/--
info:
[simps.verbose]
  adding projection Point.mul_x: ∀ (p q : Point), (p.mul q).x = p.x * q.x
[simps.verbose]
  adding projection Point.mul_y: ∀ (p q : Point), (p.mul q).y = p.y * q.y
-/
#guard_msgs (whitespace := lax) in
@[simps?] def Point.mul (p q : Point) : Point :=
  { x := p.x * q.x, y := p.y * q.y }
