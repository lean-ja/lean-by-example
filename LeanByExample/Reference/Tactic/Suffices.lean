/- # suffices

`suffices` は、数学でよくある「～を示せば十分である」という推論を行うタクティクです。

ゴールが `⊢ P` であるときに `suffices h : Q from` を実行すると、

* `suffices h : Q from` のブロック内では、仮定に `h : Q` が追加され、
* `suffices h : Q from` 以降では、ゴールが `⊢ Q` に書き換えられます。

[`apply`](./Apply.md) と似ていますが、`apply` と違って「十分条件になっていること」の証明が明らかでないときにも使うことができます。

`suffices Q from ...` という形式の場合は、証明を直接構成することが必要です。`suffices Q from by ...` とすると、タクティクによって証明を構成するモードになります。 -/
import Mathlib.Data.Nat.Order.Lemmas -- 除算 `∣` を使うため

example : 13 ∣ (2 ^ 70 + 3 ^ 70) := by
  -- 余りがゼロであることを示せば十分
  suffices goal : (2 ^ 70 + 3 ^ 70) % 13 = 0 from by
    exact Iff.mpr (Nat.dvd_iff_div_mul_eq (2 ^ 70 + 3 ^ 70) 13) rfl

  rfl
