/- # norm_num

`norm_num` は、数値リテラルを含む式を正規化するタクティクです。
閉じた数値計算や、数値だけで決まる等式・不等式・整除関係を示したいときに使います。

`norm_num` は具体的な計算を進めてゴールを閉じます。 -/
import Mathlib.Tactic.NormNum

example : (37 : Nat) * 23 + 19 = 870 := by
  norm_num

example : ¬ (15 : Int) ^ 2 < 100 := by
  norm_num

example : (2 : ℚ) / 3 + 1 / 6 = 5 / 6 := by
  norm_num

/- `norm_num` は仮定に対しても使うことができます。
たとえば `norm_num at h` とすると、仮定 `h` の中の数値計算を正規化します。 -/

example {n : Nat} (h : 3 ∣ n + 4) : 3 ∣ n + 1 := by
  -- `n + 4` は `n + 1 + 3` と同じなので、3 で割った余りは変わらない
  norm_num at h

  assumption

/- `norm_num` は `norm_num [f]` のように補題や定義を渡して使うこともできます。
渡した補題で式を展開してから、数値計算を正規化します。 -/

def taxIncluded (price : Nat) : Nat :=
  price + price / 10

example : taxIncluded 1200 = 1320 := by
  norm_num [taxIncluded]
