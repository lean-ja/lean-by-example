/- # congr

「`f₁ = f₂` かつ `a₁ = a₂` ならば `f₁ a₁ = f₂ a₂`」という事実は、等号が合同(congruence)関係であると解釈できますが、`congr` はこれを使ってゴールを分解するタクティクです。

`congr` は、`⊢ f as = f bs` という形のゴールがあったときに、ゴールを `⊢ as = bs` に変えます。再帰的に適用されるので、`⊢ g (f as) = g (f bs)` という形のゴールでも `⊢ as = bs` というゴールになります。
-/
import Mathlib.Tactic.Common -- `simp` で利用できる補題を確保するため --#

variable (X : Type) (x : Int) (f : Int → Int)

example (h : x = 0) : f (2 + x) = f 2 := by
  congr
  show 2 + x = 2

  simp [h]

/- `congr` は等号以外の関係は扱えません。等号以外の関係の合同性も扱えるタクティクに [`gcongr`](./Gcongr.md) があります。-/

variable (a b : Int)

example (h : a = b) : a + 1 = b + 1 := by
  -- 等号の場合はOK
  congr

example (h : a < b) : a + 1 < b + 1 := by
  -- 不等号の場合エラーにはならないが何も起こらない
  congr
  show a + 1 < b + 1

  exact Int.add_lt_add_right h 1

/-! ## 再帰の深さの調節

`congr` が適用される再帰の深さを引数として渡すことができます。これは、主に単に `congr` とするだけだと「行き過ぎ」になるときに調整する目的で使用されます. -/

example (g : Int → X) (h : x = 0) (hf : ∀ x, f x = f (- x)) :
    g (f (2 + x)) = g (f (- 2)) := by

  -- congr の再帰がアグレッシブすぎて上手くいかないことがある
  try
    congr

    -- 分解しすぎた
    show 2 + x = -2

    -- これでは示すことができない
    fail

  -- 再帰の深さを数値として指定できる
  congr 1

  -- ちょうどよい分解になった
  show f (2 + x) = f (-2)

  simp only [h, Nat.add_zero]
  exact hf _
