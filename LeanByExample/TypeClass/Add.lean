/- # Add

`Add` は `+` という二項演算子のための型クラスです。ここまで [`HAdd`](#{root}/TypeClass/HAdd.md) と同じですが、`HAdd` は異なるかもしれない型 `α, β, γ` に対して足し算 `(· + ·) : α → β → γ` を定義することができる一方で、`Add` は同じ型 `α` に対して足し算 `(· + ·) : α → α → α` を定義することしかできません。

`+` 記法が何を意味するかについては制約はありませんが、足し算で表される演算は可換であることが期待されるので、例外はあるものの `a + b = b + a` が成り立つような実装をすることが推奨されます。
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

  -- 記法が定義されていないので使えない
  #check_failure MyNat.zero + MyNat.zero

  -- `add` 関数を `+` の実装とする
  instance : Add MyNat where
    add := add

  -- 足し算記号が使えるようになった
  #check MyNat.zero + MyNat.zero
end MyNat
/- ## 舞台裏
`Add` 型クラスは、内部的には [`HAdd`](#{root}/TypeClass/HAdd.md) に展開されています。 -/

-- #check コマンドの出力で記法を使わないようにする
set_option pp.notation false in

/-⋆-//-- info: HAdd.hAdd MyNat.zero MyNat.zero : MyNat -/
#guard_msgs in --#
#check MyNat.zero + MyNat.zero
