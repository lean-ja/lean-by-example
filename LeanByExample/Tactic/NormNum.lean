/- # norm_num

`norm_num` は、数値リテラルを含む式を正規化するタクティクです。変数を含まない等式・不等式・整除関係等を示したいときに使います。
-/
import Mathlib.Tactic.NormNum

example : 37 * 23 + 19 = 870 := by
  norm_num

example : ¬ (15 : Int) ^ 2 < 100 := by
  norm_num

example : (2 : ℚ) / 3 + 1 / 6 = 5 / 6 := by
  norm_num

/- `norm_num` は仮定に対しても使うことができます。
たとえば `norm_num at h` とすると、仮定 `h` の中の数値式を正規化します。 -/

example {n : Nat} (h : 3 ∣ n + 4) : 3 ∣ n + 1 := by
  -- 最初は、h とゴールは違う式なので証明できない
  fail_if_success assumption

  -- `n + 4` は `n + 1 + 3` と同じなので、3 で割った余りは変わらない
  norm_num at h

  assumption

/- `norm_num` は `norm_num [f]` のように補題や定義を渡して使うこともできます。
渡した補題で式を展開してから、数値計算を正規化します。 -/

def taxIncluded (price : Nat) (taxRate : Nat) : Nat :=
  price + price * taxRate / 100

example : taxIncluded 1200 10 = 1320 := by
  -- 最初は norm_num だけでは証明が終わらない
  fail_if_success solve |
    norm_num

  norm_num [taxIncluded]
