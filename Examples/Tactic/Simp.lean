/- # simp

`simp` は，ターゲットを決められた規則に基づいて自動で簡約（simplify）するタクティクです．`@[simp]` と付けることにより簡約に使ってほしい命題を登録することができます．-/
import Mathlib.Tactic.Ring -- `ring` を使うため --#
import Mathlib.Tactic.Says -- `says` を使うために必要 --#
import Mathlib.Tactic.Tauto -- `tauto` を使うため

variable {P Q R : Prop}

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

/-! なお，`@[simp]` で登録した命題は「左辺を右辺に」簡約するルールとして登録されます．
左辺と右辺を間違えて登録すると，無限ループになって `simp` の動作が破壊されることがあるので注意してください．-/

/-! 既知の `h : P` という命題を使って簡約させたいときは，明示的に `simp [h]` と指定することで可能です．複数個指定することもできます．`simp only [h₁, ... , hₖ]` とすると `h₁, ... , hₖ` だけを使用して簡約を行います．-/

example (h : R) : (P ∨ Q ∨ R) ∧ R := by
  simp only [or_and]
  assumption

/-! 何も指定しなければゴールを簡約しますが，ローカルコンテキストにある `h : P` を簡約させたければ `simp at h` と指定することで可能です．ゴールと `h` の両方を簡約したいときは `simp at h ⊢` とします．

ローカルコンテキストとゴールをまとめて全部簡約したい場合は `simp at *` とします．-/

variable {n m : Nat}

example (h : n + 0 + 0 = m) : n = m + (0 * n) := by
  simp at h ⊢
  assumption

/-! ## simpa
`simpa` は，`simp` を実行した後 `assumption` を実行するという一連の流れを一つのタクティクにしたものです．`simpa at h` 構文は存在せず，`simpa using h` と書くことに注意してください．-/

example (h : R) : (P ∨ Q ∨ R) ∧ R := by
  simpa only [or_and]

example (h : n + 0 + 0 = m) : n = m := by
  simpa using h

/-! ## simp?

`simp` は自動的に証明を行ってくれますが，何が使われたのか知りたいときもあります．`simp?` は簡約に何が使われたのかを示してくれるので，`simp only` などを用いて明示的に書き直すことができます．-/

example : (P ∨ Q ∨ R) ∧ R ↔ R := by
  simp? says
    simp only [or_and]

/-! ## simp_arith
`simp` の設定で `arith` を有効にすると，算術的な簡約もできるようになります．
これはよく使用されるので，`simp_arith` という省略形が用意されています．
-/

example {x y : Nat} : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp (config := { arith := true, decide := true })

example {x y : Nat} : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp_arith

/-! ## simp_all

`simp_all` は `simp [*] at *` の強化版で，ローカルコンテキストとゴールをこれ以上簡約できなくなるまですべて簡約します．

## dsimp

`dsimp` は，定義上(definitionally)等しいもの同士しか簡約しないという制約付きの `simp` です．-/
