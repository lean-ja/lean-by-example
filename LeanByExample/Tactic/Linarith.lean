/- # linarith

`linarith` は線形算術(linear arithmetic)を行うタクティクです。Fourier-Motzkin elimination を用いて、線形な(不)等式系から矛盾を導こうとします。一般に、ゴールが `False` でないときにはゴールの否定を仮定に加えることで、ゴールを閉じようとします。 -/
import Mathlib.Tactic.Linarith -- `linarith` のために必要
import Batteries.Data.Rat.Basic -- `ℚ` のために必要

example (x y : ℚ) (h1: x = 2 * y) (h2 : - x + 2 * y = 1) : False := by
  linarith

example (x y z : ℚ) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) :
    12 * y - 4 * z ≥ 0 := by
  linarith

/- `linarith` はローカルコンテキストにある命題を読むので、`linarith` が通らないとき、追加で補題を示すことで解決することがあります。-/

example (x : ℚ) : id x ≤ x := by
  -- `linarith` で示すことはできない
  fail_if_success linarith

  have : id x = x := rfl

  -- `id x = x` だと教えてあげると `linarith` で示せる
  linarith

/- また、使ってほしい補題を直接渡すこともできます。-/

example (x y : ℚ) (h : x ≤ y) (pos : 0 ≤ x) : x + x ^ 2 ≤ y + y ^ 2 := by
  -- `linarith` では示せない
  fail_if_success linarith

  -- `linarith` 単独で扱えない部分、つまり `x ^ 2 ≤ y ≤ 2` を示すための
  -- 補題を引数で渡してやると通る
  linarith [pow_le_pow_left₀ pos h 2]

/- ## 舞台裏
`linarith` は一般に、型クラス `LinearOrderedCommRing` のインスタンスに対して動作します。ここで linear order とは全順序のことです。-/
section --#
variable {R : Type} [LinearOrderedCommRing R]

variable (x y z : R)

-- `R` 上の不等式だが `linarith` で証明できる
example (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) :
    12 * y - 4 * z ≥ 0 := by
  linarith

end --#
/- ## linarith と他のタクティクの使い分け
`1 < 2` のような簡単な数値のみの不等式の場合、`norm_num` や `simp` でも証明ができます。
同じ命題を示すのに複数のタクティクがあるわけですが、タクティク実行にかかる時間に違いがあります。

実行環境により正確な実行時間は異なりますが、`linarith` は比較的重いタクティクです。
-/

open Lean Elab Command in

/-- コマンドの実行時間がnミリ秒以上mミリ秒以下であることを確かめるコマンド -/
elab "#speed_test " "|" n:num "≤" "[ms]" "≤" m:num "|" stx:command : command => do
  -- 実行直前に計測開始
  let start_time ← IO.monoMsNow

  -- 与えられたコマンドを実行
  elabCommand stx

  -- 実行後に計測終了して差分をミリ秒単位で計算
  let end_time ← IO.monoMsNow
  let time := end_time - start_time

  -- 与えられた期限を取得
  let startline := n.getNat
  let deadline := m.getNat

  -- 指定時間帯に終わったかどうかを検証
  unless time ≥ startline do
    throwError m!"It took {time}ms for the command to run, which is less than {startline}ms."
  unless time ≤ deadline do
    throwError m!"It took {time}ms for the command to run, which is more than {deadline}ms."

  logInfo m!"time: {time}ms"

#speed_test
  | 10 ≤ [ms] ≤ 50
  | example : 1 < 2 := by simp

#speed_test
  | 1 ≤ [ms] ≤ 120
  | example : 1 < 2 := by norm_num

#speed_test
  | 20 ≤ [ms] ≤ 1000
  | example : 1 < 2 := by linarith
