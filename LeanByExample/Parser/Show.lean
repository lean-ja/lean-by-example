/- # show .. from

`show T from e` は、型 `T` の項 `e` を表す構文です。項に対して型 `T` を明示することができます。
-/
import Mathlib.Tactic -- 補題や `field_simp` のために import する --#

-- とても単純な使用例
#check show Nat from 1

-- `#eval` コマンドに式を渡す際に、期待される型を明示するために show を用いている例
#eval show IO Unit from do
  IO.println "Hello, world!"
  IO.println "Goodbye, world!"

/- また、Lean においては命題 `P : Prop` は型なので、命題 `P` の証明を `show P from ...` の形で構成することができます。-/

example (P : Prop) (h : P) : P :=
  show P from h

/- よく似た構文を持つものとして、[`show`](#{root}/Tactic/Show.md) タクティクがあります。-/

/- ## 用途

`show .. from` 構文を使用すると、[`have`](#{root}/Tactic/Have.md) タクティクのように補題を用意することができますが、`have` と違って補題に名前がつかず、使い捨てになります。たとえば [`rw`](#{root}/Tactic/Rw.md) タクティクに渡すために一度だけ使いたい補題があるときに有用です。 -/

variable (a b x : ℚ)

example (f : ℚ → ℕ) : f ((a + b) ^ 2) = f (a ^ 2 + 2 * a * b + b ^ 2) := by
  -- `have` をつかって補題を用意しなくても、
  -- `show ... from` で無名の証明を構成してそれを `rw` に渡すことができる
  rw [show (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 from by ring]

/- また証明項のところに **メタ変数(metavariable)** [^meta]を配置すると、証明を後回しにすることができます。 -/

example (h : a * x < b) (ha : a > 0) : x < b / a := by
  -- `b / a` を `r` とおく
  set r := b / a with hr

  -- ここで `b = a * r` というまだ示していない補題に基づいて `h` を書き換える
  rw [show b = a * r from ?lem] at h
  exact (mul_lt_mul_left ha).mp h

  -- 本来証明項が入るべきところに `?lem` をおいたので、
  -- `case lem` でフォーカスできる
  case lem =>
    -- `r` の定義を展開する
    rw [hr]

    -- 分母を払う
    field_simp

/- [^meta]: 頭に `?` がついている変数のこと。-/
