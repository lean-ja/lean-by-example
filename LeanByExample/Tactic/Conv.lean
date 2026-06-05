/- # conv

`conv` は、変換モード(conversion mode)に入るためのタクティクです。ゴールや仮定の中の特定の部分式だけを変形するために使います。
-/

/-- 何らかの自然数 -/
opaque x : Nat

axiom hx : x = x + 1

example (a : Nat) : x + a = x + 1 + a := by
  -- rw では解決できない
  -- なぜかといえば、`rw` はゴール全体にある `x` を書き換えてしまうので
  -- 右辺の `x` も `x + 1` に書き換えてしまうから
  fail_if_success solve |
    rw [hx]

  conv =>
    -- 等式の左辺 `x + a` に移動する
    lhs

    -- 左辺の `x` だけを `x + 1` に書き換える
    rw [hx]

/-
適宜 [Mathlib の conv ガイド](https://leanprover-community.github.io/mathlib4_docs/docs/Conv/Guide.html) や [Theorem Proving in Lean4](https://aconite-ac.github.io/theorem_proving_in_lean4_ja/conv.html) なども参照してください。
-/


/- ## 式の中を移動する

`conv =>` と書くと変換モードに入ります。変換モードでは、ゴールは通常の `⊢` ではなく `|` の形で表示され、現在注目している式を表します。

変換モードの中でのみ使える、式の中を移動するためのタクティクが用意されています。

* `lhs` は二項演算の左辺に移動します。
* `rhs` は二項演算の右辺に移動します。
* `congr` は現在注目している式の引数へ移動します。
* `rfl` は何もしません。式をそのままにします。

-/

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- 等式の左辺 `a * (b * c)` に移動する
    lhs

    -- `a` と `b * c` の2つに分ける
    congr

    -- `a` は書き換えない
    · rfl

    -- `b * c` だけを `c * b` に書き換える
    · rw [Nat.mul_comm]

/- ## パターンで場所を指定する

手で `lhs` や `congr` を使って移動する代わりに、`conv in パターン => ...` と書くことで書き換えたい部分式を直接指定できます。
プレースホルダ `_` も使えます。
-/

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c =>
    rw [Nat.mul_comm b c]

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c =>
    rw [Nat.mul_comm b c]

/- 同じ形の部分式が複数あるときは、`occs` で何番目の出現を書き換えるか指定できます。-/

example (a b : Nat) :
    (a + b) + (a + b) = (a + b) + (b + a) := by
  conv in (occs := 2) a + b =>
    rw [Nat.add_comm a b]
