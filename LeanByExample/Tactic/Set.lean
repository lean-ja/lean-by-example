/- # set

`set` は、ローカル変数を導入するためのタクティクです。

Lean ではローカル変数の定義に `let` をよく使いますが、`let` だと「ゴールやローカルコンテキストにある命題を導入した定義に基づいて書き換えてくれない」という不満があります。たとえば `let y := f x` としたとき、既存の `f x` を使用した部分が `y` に書き変わってはくれませんし、`y = f x` という命題の証明にアクセスでないので書き換えることもままなりません。

`set` タクティクはこうした不満に対応します。 -/
import Mathlib.Tactic.Set -- `set` のために必要

variable (X : Type) (f : Nat → Nat)
set_option linter.unusedTactic false in --#

example (x : Nat) (h : f x = x) : f (f x) = f x := by
  -- `let` を使用した場合
  try
    let y := f x

    -- ゴールは `⊢ f (f x) = f x` のままで、
    -- 導入した `y` を用いて書き換えてくれない
    show f (f x) = f x

    fail

  set y := f x with yh

  -- ゴールが書き換わる
  show f y = y

  -- 仮定も書き変わる
  guard_hyp h : y = x

  -- `y = f x` であるという事実に名前も付いている
  guard_hyp yh : y = f x

  rw [h] at *
  apply yh.symm
