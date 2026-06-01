/- # cbv

`cbv` は call-by-value evaluation (値呼び評価) に近い形で式を簡約するタクティクです。

関数の引数を先に値まで簡約してから関数本体を計算するので、Lean のコンパイラが生成するコードの実行順序に近い簡約を行います。
また、定義をそのまま展開するのではなく、定義から生成された等式定理を使って命題的な等式として書き換えるため、[`rfl`](./Rfl.md) や [`decide`](./Decide.md) では扱いづらい定義にも使えることがあります。
-/

namespace CbvExample

/- ## call by value であることの意味

`cbv` が call by value という名前なのは、関数呼び出しの引数や `if` の条件などを先に値まで簡約し、その値に応じて関数の定義方程式やパターンマッチの方程式を適用していくからです。[^ref]

ここで重要なのは、`cbv` が「定義を直接展開している」のではなく「定義方程式を使って命題的な等式として書き換えている」という点です。
整礎再帰や `partial_fixpoint` で定義された関数は、[`[irreducible]`](#{root}/Attribute/Irreducible.md) 属性によって定義的には展開しづらくなります。
しかし、その関数を値呼びで実行したときの計算規則に対応する定義方程式は利用できます。
そのため `cbv` は、値呼びで実行したときに起こる計算を、定義的等価性ではなく等式による書き換えとして再現できるのです。
-/

/- ## 整礎再帰で定義された関数に使う

整礎再帰を使って定義された関数は、自動的に [`[irreducible]`](#{root}/Attribute/Irreducible.md) 属性が付与されます。
そのため、定義的等価性だけを見る [`rfl`](./Rfl.md) では証明できないことがあります。
-/

/-- 文字列を指定した長さになるまで左側から特定の文字で埋める関数 -/
def padWith (s : String) (c : Char) (n : Nat) : String :=
  if n ≤ s.length then
    s
  else
    padWith (c.toString ++ s) c n
termination_by n - s.length

-- 値としては期待通りに計算できる
#guard padWith "abc" 'x' 5 = "xxabc"

example : padWith "abc" 'x' 5 = "xxabc" := by
  -- 整礎再帰で定義された関数なので `rfl` では示せない
  fail_if_success rfl

  -- `decide` でも示せない
  fail_if_success decide

  -- `cbv` なら定義方程式を使って簡約できる
  cbv

/- `cbv` は等式ゴールを簡約したあと、両辺が同じになれば自動でゴールを閉じます。
閉じられない場合でも、ゴールは簡約された状態で残ります。 -/

example (n : Nat) : (fun m => m + 1) n = n.succ := by
  -- `cbv` で左辺の関数適用が簡約される
  cbv

/- ## 仮定に対して使う

`cbv` は多くの書き換え系タクティクと同じように、`at` 構文で仮定を対象にできます。
-/

example (h : padWith "abc" 'x' 5 = "xxabc") (P : Prop) (hp : P) : P := by
  have _ : padWith "abc" 'x' 5 = "xxabc" := h

  -- 仮定 h の中の `padWith "abc" 'x' 5` を簡約する
  cbv at h

  guard_hyp h : True

  exact hp

/- ## native_decide との違い

[`native_decide`](./NativeDecide.md) も計算で証明できる命題を示せますが、Lean のコンパイラを信頼する必要があります。
一方で `cbv` は等式定理による書き換えとして証明を構成するため、コンパイラの正しさに依存しません。
-/

theorem padWith_cbv : padWith "abc" 'x' 5 = "xxabc" := by
  cbv

/-- info: 'CbvExample.padWith_cbv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in --#
#print axioms padWith_cbv

end CbvExample

/- [^ref]: Lean 公式リファレンスの `cbv` の説明を参考にしています。
<https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#call-by-value-evaluation> -/
