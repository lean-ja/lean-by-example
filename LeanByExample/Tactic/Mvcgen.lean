/- # mvcgen

`mvcgen` は、モナディック(monadic)なプログラムを含むゴールを **検証条件(verification condition)** に分解して処理するようなタクティクです。ただしここでいう検証条件とは、`do` 構文の背景にあるモナドを参照しない部分ゴールのことを指します。[^mvcgen-doc]

`do` 構文を使って手続き的に定義された関数に対して証明を行うことを支援するフレームワークが Lean には組み込まれているのですが、`mvcgen` はその一部です。

シンプルな使用例として、リストの和を `for` ループを使って計算する関数が、標準ライブラリに用意されている関数と等しいことを `mvcgen` を使って証明する例を紹介します。このとき、ループを回しても変わらずに成り立ち続ける **不変条件(invariant)** を指定することに注意してください。
-/
import Lean

-- mvcgen はまだ使用しないでというwarningを消す
set_option mvcgen.warning false

variable {α : Type} [Zero α] [Add α]
variable [@Std.Associative α (· + ·)] [@Std.LawfulIdentity α (· + ·) 0]

/-- for文を使って命令的に実装された、和を計算する関数 -/
@[grind]
def sumDo (l : List α) : α := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

-- 証明の中で必要になる補題
@[grind =, simp]
theorem List.sum_append_singleton {l : List α} {x : α} :
    (l ++ [x]).sum = l.sum + x := by
  induction l with simp_all <;> grind

-- `scoped` で用意された表記法を有効にする
open Std.Do

/-- 手続き的に実装した和の計算と、標準ライブラリに用意されている`List.sum`関数が等しい -/
theorem sumImp_eq_sumFunc (l : List α) : sumDo l = List.sum l := by
  -- モナディックに実装されている（`Id.run do ...`）部分にフォーカスする
  generalize h : sumDo l = s
  apply Id.of_wp_run_eq h

  -- 検証条件に分解する
  mvcgen

  -- ループ全体を通して成り立たせたい不変条件を指定する
  -- * `out` は `let mut` で導入した変数の現在値を表す
  -- * `xs` は `List.Cursor` で，リストを接頭辞 `xs.prefix` と接尾辞 `xs.suffix` に
  --   分割して表すデータ構造。どこまでループが進んだかを追跡する。
  --   つまり進捗（ループの到達位置）を記録する。
  -- 不変条件は「`out` が接頭辞の総和を保持している」こと。
  -- 記法 `⌜p⌝` は，純粋な命題 `p : Prop` をアサーション言語に埋め込む。
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝

  -- `mleave` はある決まった `simp` 補題に対する `simp only [...] at *` の糖衣構文。
  all_goals mleave

  -- 各反復で不変条件が保たれることを示す
  case vc1.step pref cur suff hyp b ih =>
    -- 与えられているリストは
    -- * `pref`: for 文で既に処理された部分
    -- * `cur`: 今回処理する要素
    -- * `suff`: まだ処理されていない残りの部分
    -- に分割されているという仮定がある。
    guard_hyp hyp :ₛ l = pref ++ cur :: suff

    -- そして今まで処理された部分に関しては不変条件が成り立っているという帰納法の仮定がある
    guard_hyp ih :ₛ pref.sum = b

    -- このとき、現在の要素 `cur` を処理した後でも不変条件が成り立つことを示せばよい
    guard_target =ₛ (pref ++ [cur]).sum = b + cur

    -- 証明そのものは `grind` で終わる
    grind

  -- ループ開始時に不変条件が成り立つことを示す
  case vc2.a.pre =>
    -- 空リストの和が 0 であることを示せばよい
    guard_target =ₛ ([] : List α).sum = 0

    grind

  -- ループ終了時の不変条件から目標の性質が従うことを証明する
  case vc3.a.post.success result hr =>
    -- ループ終了時には「処理された部分」は全体なので、
    -- 不変条件から次が成りたつ
    guard_hyp hr :ₛ l.sum = result

    -- したがって目標も成り立つ
    grind

/- ## 構文

`mvcgen` タクティクを使用するとき、まず不変条件を指定し、そのあとに `all_goals mleave` を実行するというパターンがよく見られます。そこで、定型文を減らすために以下のように `mvcgen invariants` という構文が用意されています。

{{#include ./Mvcgen/NaiveExpo.md}}
-/

/- ## 使用例

### 早期リターン

`for` 文の途中で `return` 文があるような場合でも、`mvcgen` は対応できます。その場合は不変条件の書き方が変わって、「早期終了した場合」と「早期終了せず継続する場合」の２つを考慮する必要が生じます。

{{#include ./Mvcgen/NoDup.md}}
-/

/- ### 早期リターン 2

早期リターンを利用するような例をもう一つ挙げましょう。整数のリストに対して、前から順に足していったときに和が0未満になる瞬間があるかチェックする関数について仕様を証明する例です。[^below-zero]

{{#include ./Mvcgen/BelowZero.md}}
-/

/-
[^mvcgen-doc]: このページの内容およびコード例は、公式のドキュメントである [Verifying imperative programs using mvcgen](https://hackmd.io/@sg-fro/BJRlurP_xg) を参考にしています。
[^below-zero]: このコード例は [human-eval-lean](https://github.com/leanprover/human-eval-lean) のコードを参考にしています。
-/
