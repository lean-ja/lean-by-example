/- # conv

`conv` は、ゴールや仮定の中の特定の部分式だけを変形するためのタクティクです。
変換モード(conversion mode)に入ると、通常のタクティクモードとは違って「現在注目している式」を移動しながら、そこに `rw` や `simp` を適用できます。

[`rw`](./Rw.md) はゴール全体にある書き換え対象を探しますが、複雑な式の奥にある特定の出現だけを書き換えたいときや、束縛変数の内側を書き換えたいときには `conv` が便利です。

詳細な仕様については [Mathlib の conv ガイド](https://leanprover-community.github.io/mathlib4_docs/docs/Conv/Guide.html) や [Theorem Proving in Lean4](https://aconite-ac.github.io/theorem_proving_in_lean4_ja/conv.html) を参照してください。
-/
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SimpRw

/- ## 式の中を移動する

`conv =>` と書くと変換モードに入ります。変換モードでは、ゴールは通常の `⊢` ではなく `|` の形で表示され、現在注目している式を表します。

たとえば `lhs` は等式の左辺に移動し、`rhs` は右辺に移動します。
`congr` は現在注目している式の引数へ移動するために使えます。不要な場所は `rfl` でそのままにします。
-/

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- 等式の左辺 `a * (b * c)` に移動する
    lhs

    -- `a` と `b * c` の2つに分ける
    congr

    -- `a` は書き換えない
    rfl

    -- `b * c` だけを `c * b` に書き換える
    rw [Nat.mul_comm]

/- ## パターンで場所を指定する

手で `lhs` や `congr` を使って移動する代わりに、`conv in パターン => ...` と書くことで書き換えたい部分式を直接指定できます。
プレースホルダ `_` も使えます。
-/

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c =>
    rw [Nat.mul_comm]

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c =>
    rw [Nat.mul_comm]

/- 同じ形の部分式が複数あるときは、`occs` で何番目の出現を書き換えるか指定できます。
出現番号は左から右へ、外側から内側へ数えます。 -/

example (a b : Nat) :
    (a + b) + (a + b) = (a + b) + (b + a) := by
  conv in (occs := 2) a + b =>
    rw [Nat.add_comm]

/- ## `simp` が難しい形を狙って書き換える

`conv in ...` は、ゴールの中の命題や等式をパターンで探して、その中だけを書き換えることもできます。
次の例では、存在記号の内側にある等式の右辺だけを `omega` で得た補題によって `2` に変形しています。
-/

example : ∃ m n, n = 1 + 1 + m - m := by
  conv in _ = _ =>
    rw [show ∀ m, 1 + 1 + m - m = 2 from by omega]

  exists 100000, 2

/- ## 束縛変数の内側を書き換える

`rw` はラムダ抽象などの束縛変数の内側まで常に探すわけではありません。
そのような場面では、`simp_rw` や `conv` が使えます。

次の例では、`fun x => ...` の内側にある `List.count x (h :: tl)` を `List.count_cons` で書き換えたいのですが、単なる `rw` では届きません。
-/

open List

variable {α : Type*} [DecidableEq α]

example (h : α) (tl : List α) :
    map (fun x => count x (h :: tl)) tl =
      map (fun x => count x tl + if h == x then 1 else 0) tl := by
  -- `rw` はラムダの内側にある `count x (h :: tl)` に届かない
  fail_if_success rw [List.count_cons]

  -- `simp_rw` なら束縛変数の内側も書き換える
  simp_rw [List.count_cons]

/- `conv` でも、書き換えたい部分式をパターンで指定すれば同じことができます。 -/

example (h : α) (tl : List α) :
    map (fun x => count x (h :: tl)) tl =
      map (fun x => count x tl + if h == x then 1 else 0) tl := by
  conv in count _ (h :: tl) =>
    rw [List.count_cons]

/- `conv` は自動化というより「どこを書き換えるか」を明示するための道具です。
単に全体を単純化したいときは [`simp`](./Simp.md)、指定した補題を束縛変数の内側まで反復的に使いたいときは `simp_rw`、書き換える場所を人間が正確に指定したいときは `conv`、という使い分けになります。 -/
