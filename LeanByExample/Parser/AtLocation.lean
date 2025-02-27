import Mathlib.Tactic --#
/- # at 構文

`at` 構文とは、タクティク `tac` に対してその書き換え対象を指定する構文のことです。[`rw`](#{root}/Tactic/Rw.md) タクティクや [`simp`](#{root}/Tactic/Simp.md) タクティクなど、「書き換え」を行う多くのタクティクがこの構文を受け入れるようになっています。

## 利用可能な構文

### at h

ローカルコンテキストにある仮定 `h : P` に対して `at h` と書くことで `h` に対して書き換えを行うことができます。
-/
section
  variable {a b : Nat}

  example (lem : a + 0 = a) (h : a + (a + 0) = a) : a + a = a := by
    -- ローカルコンテキストの `h` に対して書き換えを行う
    rw [lem] at h

    rw [h]

end
/- ### at h₁ h₂ ..

また、ローカルコンテキストにある複数の仮定 `h₁, h₂, ..` に対して書き換えを行うには空白区切りで `at h₁ h₂ ..` とします。 -/
section
  variable (x m n : ℕ)

  example (left : (x : ℝ) < ↑m + ↑n) (right : ↑m + ↑n < (x : ℝ) + 1) : False := by
    -- `left`と`right`に対して書き換えを行う
    norm_cast at left right

    omega
end
/- ### at h ⊢
ローカルコンテキストにある仮定 `h : P` とゴールに対して同時に書き換えを行うには、`at h ⊢` とします。 -/

example (x : Nat) (h : x ≥ 1) : 2 * x ≥ 2 := by
  -- 自然数から有理数にキャストする
  qify at h ⊢

  have : (2 : ℚ) ≤ 2 * x := calc
    _ = 2 * 1 := by simp
    _ ≤ 2 * (x : ℚ) := by gcongr
  assumption
/- ### at *

ローカルコンテキストのすべての仮定とゴールに対して書き換えを行うには、`at *` とします。
-/
section
  set_option linter.flexible false

  variable (P : Nat → Bool)

  example (h1 : P (if 0 = 0 then 1 else 2)) (h2 : P (0 * 1)) : P 0 ∧ P (1 + 0) := by
    simp at *

    exact ⟨h2, h1⟩
end
/- ## at 構文を受け入れるタクティクを作る

次に示すのは `at` 構文を受け入れるようなタクティクをマクロとして構成する例です。
-/

/-- 自前で定義した狭義順序 -/
def Nat.mylt (m n : Nat) : Prop := (m + 1) ≤ n

/-- 単に `m < n` と書いたら上で定義した自前の順序が使われるようにする -/
instance : LT Nat where
  lt m n := m.mylt n

open Lean.Parser.Tactic in

/-- `(· < ·)`を定義に展開して中身を確認するための専用自作タクティク -/
syntax (name := dsimp_lt) "dsimp_lt" (location)? : tactic

macro_rules
  | `(tactic| dsimp_lt $[at $location]?) =>
    `(tactic| dsimp only [(· < ·), Nat.mylt] $[at $location]?)

example : 1 < 4 := by
  dsimp_lt
  guard_target =ₛ 1 + 1 ≤ 4

  decide

example (_h : 1 < 3) : True := by
  dsimp_lt at _h
  guard_hyp _h : 1 + 1 ≤ 3

  trivial
