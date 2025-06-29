/- # dsimproc

`dsimproc` は、simpプロシージャを宣言するためのコマンドの一つです。

simpプロシージャは、ある式 `expr` にマッチする部分を見つけたときに、より単純な式 `result` を動的に計算し、`expr = result` の証明も同時に構成するような、`simp` タクティクから呼び出される書き換え規則のことです。

`dsimproc` は simpプロシージャを定義するものですが、定義的に等しい(definitionally equal)変形だけを行います。
したがって、`expr = result` の証明が不要です。(`rfl` を使うだけで済むので)

以下は、具体的な数値に対する関数呼び出しを計算して単純化するようなシンプルな simp プロシージャを定義する例です。
-/
import Lean

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
  simp at h
  assumption

example (P : Nat → Prop) (h : P (Nat.fib 5)) : P 5 := by
  -- `simp_all`からも呼び出される
  simp_all
