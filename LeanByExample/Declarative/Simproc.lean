/- # simproc

`simproc` コマンドは、simproc を宣言するコマンドの一つです。

simproc は、ある式 `expr` にマッチする部分を見つけたときに、より単純な式 `result` を動的に計算し、`expr = result` の証明も同時に構成するような、`simp` タクティクから呼び出される書き換え規則のことです。

## 使用例

たとえば、`simp` タクティクには if 式に対する単純化機能が標準で備わっていますが、これを行う simproc を自前で定義してみましょう。
-/
import Lean
import Qq

example : (if 1 = 1 then 2 else 3) = 2 := by
  -- if式の単純化を行うことができる
  simp

/- まず前段階として、標準の if と混ざらないように if 式そのものを自前で構成します。-/
section

  variable {α : Type}

  /-- 標準の`ite`(if式の内部実装)を真似て自作したもの -/
  def myIte (cond : Prop) [h : Decidable cond] (t e : α) : α :=
    match decide cond with
    | true => t
    | false => e

  @[inherit_doc myIte]
  notation "mif " cond " then " t " else " e => myIte cond t e

  -- 動作テスト
  #guard (mif 1 < 2 then 3 else 4) == 3
  #guard (mif 1 = 2 then 3 else 4) == 4

  variable (cond : Prop) [h : Decidable cond]

  /-- 条件式が真なら、mif式は`then`部分に等しい -/
  theorem myIte_cond_eq_true (t e : α) (i : cond = True) : myIte cond t e = t := by
    dsimp [myIte]
    have : decide cond = true := by simp_all
    rw [this]

  /-- 条件式が偽なら、mif式は`else`部分に等しい -/
  theorem myIte_cond_eq_false (t e : α) (i : cond = False) : myIte cond t e = e := by
    dsimp [myIte]
    have : decide cond = false := by simp_all
    rw [this]

end
/- 続いて、simproc の本体を構成します。単に単純化の結果を返せばよいわけではなく、元の式との等価性を証明する必要があることに気を付けてください。[^reduceMyIte] -/

open Lean Meta Simp Qq

/-- `mif`式を単純化するsimproc。 -/
simproc ↓reduceMyIte (myIte _ _ _) := .ofQ fun u _α expr => do
  -- パターンマッチ。`myIte _ _ _`の形であることを確認する。
  -- そうでなければ即終了する。
  match u, α, expr with
  | 1, _, ~q(@myIte _ $cond $h $t $e) =>
    -- 条件式の部分を単純化する
    have simp_cond : Result := ← simp cond -- 右辺が`Qq`を使用していないので`have`を使う
    have simp_cond_prop : Q(Prop) := simp_cond.expr
    trace[debug] "条件式の部分が {simp_cond_prop} に単純化されました。"

    -- 単純化された結果`cond`が`True`または`False`として評価されていなければ、
    -- その時点で終了する
    if !simp_cond_prop.isTrue && !simp_cond_prop.isFalse then
      return .continue

    -- 単純化なので`cond = simp_cond_prop`という命題が成り立つ。
    -- その証明を取得して名前を付けておく。
    have cond_eq_simp_cond : Q($cond = $simp_cond_prop) := ← simp_cond.getProof
    trace[debug] "条件式に対して {← inferType cond_eq_simp_cond} という単純化が行われました。"

    -- 条件式が真と評価された場合
    if simp_cond_prop.isTrue then
      -- このとき`simp_cond_prop`は`True`であることを`Qq`に教えておく
      have : $simp_cond_prop =Q True := ⟨⟩

      -- このとき`myIte cond t e = t`が成り立つので、結果の`Expr`としては`t`を返すべき。
      have result_expr := t
      trace[debug] "{expr} を単純化した結果は {result_expr} であるべきです。"

      -- 結果の`Expr`が元の`Expr`と同じであることの証明も必要。
      -- つまり`myIte cond t e = t`の証明が必要。
      let target : Q(Prop) := q(myIte $cond $t $e = $t) -- 証明したい命題
      trace[debug] "単純化のために {target} を証明する必要があります。"

      -- `target`の証明を構成する。
      -- これは定理`myIte_cond_eq_true`を使って構成できる。
      let target_proof : Q($target) := q(myIte_cond_eq_true $cond $t $e $cond_eq_simp_cond)
      trace[debug] "{← inferType target_proof} の証明を構成しました。"
      return .visit { expr := result_expr, proof? := target_proof }

    -- 条件式が偽と評価された場合(説明は省略)
    if simp_cond_prop.isFalse then
      have : $simp_cond_prop =Q False := ⟨⟩
      have result_expr := e
      let target_proof := q(myIte_cond_eq_false $cond $t $e $cond_eq_simp_cond)
      return .visit { expr := result_expr, proof? := target_proof }

    return .continue

  | _, _, _ =>
    return .continue

-- これで`[debug]`とマークされたトレースメッセージが表示される
set_option trace.debug true

/-⋆-//--
trace: [debug] 条件式の部分が True に単純化されました。
[debug] 条件式に対して (1 < 1 + 1) = True という単純化が行われました。
[debug] mif 1 < 2 then 3 else 4 を単純化した結果は 3 であるべきです。
[debug] 単純化のために (mif 1 < 2 then 3 else 4) = 3 を証明する必要があります。
[debug] (mif 1 < 2 then 3 else 4) = 3 の証明を構成しました。
-/
#guard_msgs in --#
example : (mif 1 < 2 then 3 else 4) = 3 := by
  simp

example : (mif 1 = 2 then 3 else 4) = 4 := by
  simp

/- [^reduceMyIte]: こちらのコードを書くにあたり、Zulip 上で Eric Wieser 氏に多くの助言をいただきました。ありがとうございました。 -/
