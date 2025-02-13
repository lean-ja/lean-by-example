/- # Mul

`Mul` は `*` という二項演算子のための型クラスです。`*` 記号が何を意味するかについての制約はありません。ここまで [`HMul`](#{root}/TypeClass/HMul.md) と同じですが、`HMul` は異なるかもしれない型 `α, β, γ` に対して掛け算 `(· * ·) : α → β → γ` を定義することができる一方で、`Mul` は同じ型 `α` に対して掛け算 `(· * ·) : α → α → α` を定義することしかできません。
-/

/-- 自前で定義した自然数 -/
inductive MyNat where
  | zero
  | succ (n : MyNat)

namespace MyNat
  /- ## MyNat の足し算を定義する -/

  def add (m n : MyNat) : MyNat :=
    match n with
    | zero => m
    | succ n => succ (add m n)

  -- `add` 関数を `+` の実装とする
  instance : Add MyNat where
    add := add

end MyNat

namespace MyNat
  /- ## MyNat の掛け算を定義する -/

  def mul (m n : MyNat) : MyNat :=
    match n with
    | zero => zero
    | succ n => (mul m n) + n

  -- 記法が定義されていないので使えない
  #check_failure MyNat.zero * MyNat.zero

  -- `mul` 関数を `*` の実装とする
  instance : Mul MyNat where
    mul := mul

  -- 掛け算記号が使えるようになった
  #check MyNat.zero * MyNat.zero
end MyNat
/- ## 舞台裏

`Mul` 型クラスは、内部的には [`HMul`](#{root}/TypeClass/HMul.md) に展開されています。
-/
-- #check コマンドの出力で記法を使わないようにする
set_option pp.notation false in

/-⋆-//-- info: HMul.hMul MyNat.zero MyNat.zero : MyNat -/
#guard_msgs in --#
#check MyNat.zero * MyNat.zero
