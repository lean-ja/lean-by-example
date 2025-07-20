/- # dsimproc

`dsimproc` は、simproc を宣言するためのコマンドの一つです。

simproc は、ある式 `expr` にマッチする部分を見つけたときに、より単純な式 `result` を動的に計算し、`expr = result` の証明も同時に構成するような、`simp` タクティクから呼び出される書き換え規則のことです。

`dsimproc` は simproc を定義するものですが、**定義的等価(definitionally equal)** な変形だけを行います。
したがって、`expr = result` の証明が不要です。(`rfl` を使うだけで済むので)

以下は、具体的な数値に対する関数呼び出しを計算して単純化するようなシンプルな simproc を定義する例です。
-/
import Lean
import Qq --#

def Nat.fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

example (P : Nat → Prop) (h : P (Nat.fib 5)) : P 5 := by
  -- 最初は simp が使えない
  fail_if_success simp at h

  have : Nat.fib 5 = 5 := by rfl
  simp [this] at h
  assumption

dsimproc computeFib (Nat.fib _) := fun e => do
  -- パターンマッチ。`e : Expr` が `Nat.fib n` の形であることを確認する
  -- そうでなければ即終了する
  let_expr Nat.fib m ← e
    | return .continue

  -- `m` が自然数リテラルであることを確認する
  -- もしそうでなければ即終了する
  let some n := m.nat?
    | return .continue

  -- `Nat.fib n` を評価する
  let l := Nat.fib n

  return .visit <| Lean.toExpr l

-- 単純化をやってくれる
example (P : Nat → Prop) (h : P (Nat.fib 5)) : P 5 := by
  dsimp at h
  assumption

example (P : Nat → Prop) (h : P (Nat.fib 5)) : P 5 := by
  -- `simp_all`からも呼び出される
  simp_all

/- ## 用途

simp 補題による書き換えでは無数に多くの補題を必要としそうな場合であっても、simproc を使うことで綺麗に解決できることがあります。[^unfoldNat]
-/

open Lean Meta Qq in

/-- 数値リテラル `n` を `1 + 1 + ⋯ + 1` という形に展開する

**注意**: このsimprocが常に適用されると困るので、実際には`dsimproc_decl`を使った方が良い。
-/
dsimproc unfoldNat ((_)) := fun e => do
  -- 自然数リテラルでなければ即終了する
  let_expr OfNat.ofNat _ num inst := e
    | return .continue
  let some n := num.rawNatLit?
    | return .continue

  -- その自然数リテラルが自然数を表しているのでなければ即終了する
  let num : Q(Nat) := num
  unless ← isDefEq inst q(instOfNatNat $num) do
    return .continue

  -- `1 + 1 + ⋯ + 1` の形に展開する
  let mut result : Q(Nat) := q(1)
  let mut n := n
  while n > 1 do
    result := q($result + 1)
    n := n - 1
  return .done result

example (a : Nat) : 3 * a = 1 * a + 2 * a := by
  dsimp only [unfoldNat]
  guard_target =ₛ (1 + 1 + 1) * a = 1 * a + (1 + 1) * a
  grind

example (a : Nat) : (2 : Int) * a = a + a := by
  -- 自然数を表す自然数リテラルは存在しないので失敗する
  fail_if_success dsimp only [unfoldNat]
  grind

/-
[^unfoldNat]: このコード例は、Robin Arnez さんに教えていただいたものを参考にしています。
-/
