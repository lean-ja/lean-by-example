/- # split

仮定やゴールにある `if ... then ... else` や `match ... with ...` 式を扱うのに有用なタクティクです。

`if/match` 式を扱う必要が生じるのは、典型的には Lean で定義したアルゴリズムや関数に関して、何か性質を証明しようとしたときです。

ゴールが `⊢ Q (if P then a else b)` であったときに、`split` を使用すると次のように2つのサブゴールが生成されます。

* 1つはローカルコンテキストに `† : P` が追加され、ゴールが `⊢ Q (a)` になったもの。
* 1つはローカルコンテキストに `† : ¬ P` が追加され、ゴールが `⊢ Q (b)` になったもの。

`split` によって追加される仮定は名前がついているとは限りません。名前がついていなかった場合、`case` などで名前を付けることができます。

仮定に対して用いる場合は `split at h` のように利用します。 -/
import Mathlib.Tactic.Set -- `set` のために必要 --#
import Mathlib.Tactic.Linarith -- `linarith` を使うため --#

-- if 式を使って関数を定義する
def myabs (x : Int) : Int :=
  if x ≥ 0 then x else - x

example (x : Int) : myabs (2 * x) = 2 * myabs x := by
  -- `myabs` の定義を展開する
  dsimp [myabs]

  -- ゴールの中に if 式があって複雑
  show (if 2 * x ≥ 0 then 2 * x else -(2 * x)) = 2 * if x ≥ 0 then x else -x

  -- `split` タクティクでケース分割する
  split

  case isTrue h =>
    -- `2 * x ≥ 0` の場合
    guard_hyp h: 2 * x ≥ 0

    -- 左辺にあった if 式が消えた
    show 2 * x = 2 * if x ≥ 0 then x else -x

    replace h : x ≥ 0 := by linarith [h]

    -- `simp` で if を消すことができる
    simp [h]

  case isFalse h =>
    -- `2 * x < 0` の場合
    guard_hyp h: ¬2 * x ≥ 0

    -- 左辺にあった if 式が消えた
    show -(2 * x) = 2 * if x ≥ 0 then x else -x

    -- if 式を消すための補題を準備する
    have hx : ¬ x ≥ 0 := by linarith [h]

    -- `simp` で単純化
    simp [h, hx]

/- ## match 式と split
`if` 式だけでなく `match` 式に対しても使うことができます。
-/

-- match式を使って関数を定義する
def mysgn (x : Int) :=
  match x with
  | Int.negSucc _ => -1
  | Int.ofNat 0 => 0
  | _ => 1

example (x : Int) : mysgn (mysgn x) = mysgn x := by
  -- mysgn x を k と置く
  set k := mysgn x with h
  -- h の mysgn の定義を展開する
  dsimp [mysgn] at h
  -- h の match の結果によって場合分け
  -- すべての場合 (k = -1, 0, 1) に関して mysgn の定義に従い計算する
  split at h
  all_goals
    rw [h]
    rfl
