/- # simp

`simp` は，ターゲットを決められた規則に基づいて自動で単純化（simplify）するタクティクです．`@[simp]` と付けることにより単純化に使ってほしい命題を登録することができます．-/
import Mathlib.Tactic.Ring -- `ring` を使うため --#
import Mathlib.Tactic.Says -- `says` を使うために必要 --#
import Mathlib.Tactic.Tauto -- `tauto` を使うため
namespace Simp --#

variable {P Q R : Prop}

example : (P ∨ Q ∨ R) ∧ R ↔ R := by
  -- simp だけでは証明が終わらない
  simp
  show R → P ∨ Q ∨ R

  -- 残りを適当に証明する
  intro hR
  tauto

@[simp]
theorem or_and : (P ∨ Q ∨ R) ∧ R ↔ R := by
  constructor

  -- 左から右を示す
  case mp =>
    intro ⟨_, hR⟩
    assumption

  -- 右から左を示す
  case mpr =>
    -- R が成り立つと仮定する
    intro hR

    -- R は成り立つので，後は P ∨ Q ∨ R が成り立つことを示せばよい
    refine ⟨?_, hR⟩

    -- R が成り立つことから明らか．
    tauto

-- 一度登録した命題は `simp` で示せるようになる．
example : (P ∨ Q ∨ R) ∧ R ↔ R := by simp

/-! なお，`@[simp]` で登録した命題は「左辺を右辺に」単純化するルールとして登録されます．
左辺と右辺を間違えて登録すると，無限ループになって `simp` の動作が破壊されることがあります．`simp` 補題は慎重に登録してください．-/
section

-- 何もしていなければ simp で通る
example (n m : Nat) : (n + 0) * m = n * m := by simp

-- 良くない simp 補題の例
-- 「左辺を右辺に」単純化するため，かえって複雑になってしまう
-- なお local を付けているのは，この simp 補題登録の影響をセクション内に限定するため
@[local simp]
theorem bad_add_zero (n : Nat) : n = n + 0 := by rw [Nat.add_zero]

-- 今まで通った証明が通らなくなる
/--
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (n m : Nat) : (n + 0) * m = n * m := by simp

end
/-! ## simp で使用できる構文

既知の `h : P` という命題を使って単純化させたいときは，明示的に `simp [h]` と指定することで可能です．複数個指定することもできます．また `simp only [h₁, ... , hₖ]` とすると `h₁, ... , hₖ` だけを使用して単純化を行います．-/

example (h : R) : (P ∨ Q ∨ R) ∧ R := by
  simp only [or_and]
  assumption

/-! 何も指定しなければゴールを単純化しますが，ローカルコンテキストにある `h : P` を単純化させたければ `simp at h` と指定することで可能です．ゴールと `h` の両方を単純化したいときは `simp at h ⊢` とします．-/

variable {n m : Nat}

example (h : n + 0 + 0 = m) : n = m + (0 * n) := by
  simp at h ⊢
  assumption

/- ローカルコンテキストとゴールをまとめて全部単純化したい場合は `simp at *` とします． -/

/-! ## simpa
`simpa` は，`simp` を実行した後 `assumption` を実行するという一連の流れを一つのタクティクにしたものです．`simpa at h` 構文は存在せず，`simpa using h` と書くことに注意してください．-/

example (h : R) : (P ∨ Q ∨ R) ∧ R := by
  simpa only [or_and]

example (h : n + 0 + 0 = m) : n = m := by
  simpa using h

/-! ## simp?

`simp` は自動的に証明を行ってくれますが，何が使われたのか知りたいときもあります．`simp?` は単純化に何が使われたのかを示してくれるので，`simp only` などを用いて明示的に書き直すことができます．-/

example : (P ∨ Q ∨ R) ∧ R ↔ R := by
  simp? says
    simp only [or_and]

/-! ## simp_arith
`simp` の設定で `arith` を有効にすると，算術的な単純化もできるようになります．
これはよく使用されるので，`simp_arith` という省略形が用意されています．
-/

example {x y : Nat} : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  -- `simp` だけでは証明が終わらない
  simp
  show y ≤ x + y + 1

  -- 残りを適当に証明する
  calc y = 0 + y := by simp
    _ ≤ x + 1 + y := by gcongr; simp
    _ = x + y + 1 := by ac_rfl

example {x y : Nat} : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  -- config を与えれば一発で終わる
  simp (config := { arith := true, decide := true })

example {x y : Nat} : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp_arith

/-! ## simp_all

`simp_all` は `simp [*] at *` の強化版で，ローカルコンテキストとゴールをこれ以上単純化できなくなるまですべて単純化します．

## simps 属性
補題を `simp` で使えるようにするのは `@[simp]` タグを付けることで可能ですが，`simps` 属性(または `@[simps]` タグ)を利用すると `simp` で使用するための補題を自動的に生成してくれます．これは Mathlib で定義されている機能であり，使用するには `Mathlib.Tactic.Basic` の読み込みが必要です．

例えば，ユーザが `Point` という構造体を定義し，`Point` 上の足し算を定義したところを考えましょう．このとき，足し算はフィールドの値の足し算で定義されているため，「`Point` の和の `x` 座標」は `x` 座標の和ですが，これはそのままでは `simp` で示すことができません．`simps` 属性を `Point.add` 関数に付与することで，`simp` で示せるようになります．
-/

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

-- `Point.add` に `simps` 属性を付与する
attribute [simps] Point.add

example (a b : Point) : (Point.add a b).x = a.x + b.x := by
  -- simp で示せるようになった
  simp

/- `@[simps?]` に換えると，生成された補題を確認することができます．-/

/--
info: [simps.verbose] adding projection Simp.Point.sub_x:
      ∀ (p q : Simp.Point), (p.sub q).x = p.x - q.x
[simps.verbose] adding projection Simp.Point.sub_y: ∀ (p q : Simp.Point), (p.sub q).y = p.y - q.y
-/
#guard_msgs (whitespace := lax) in
@[simps?] def Point.sub (p q : Point) : Point :=
  { x := p.x - q.x, y := p.y - q.y }

end Simp --#
