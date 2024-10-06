/- # 「ならば」の定義を疑う

## イントロダクション

論理学を学び始めた初心者がよく抱く疑問の一つに、「『ならば』の定義に納得がいかない」というのがあります。「P ならば Q」は論理学や Lean では P が偽ならば Q が何であっても真であるものとして定義しますが、それが直観に反するという疑問です。

自然言語における「ならば」は、あまりこのような使い方をしませんので、確かに違和感がありますね。たとえば、「意味が分かると怖い話」の中にただただ意味不明なだけの話は普通含まれませんよね！

この演習問題では、この疑問に対する一つの答えを提示します。つまり、含意が満たしていて欲しい最低限の性質をいくつか列挙し、それを満たす「何か」の定義はただ一つしかないということを確認します。

## 含意が満たしていて欲しい性質

まずは、含意に相当する「何か」を定義しましょう。それは、命題から命題への2変数関数になっているとします。ここではその何かに `Imp` という名前をつけ、`→ᵥ` という記号で表すことにします。
-/
import Lean --#
set_option autoImplicit false --#
set_option relaxedAutoImplicit false --#
-- 含意が満たすべき性質を満たす「何か」
opaque Imp (P Q : Prop) : Prop

-- 含意っぽい記法の導入
-- `v` は `virtual` の略
infixr:40 " →ᵥ " => Imp

/- これだけだと型があるだけで中身がないので、性質を与えていきましょう。含意が満たしているべき性質とはなんでしょうか？ `P →ᵥ Q` がおおよそ「`P` を仮定すると `Q` が示せる」という意味になるようにしたいと考えると、次のようなものが考えられるでしょう。 -/
namespace Imp --#

variable {P Q R : Prop}

/-- 含意は反射的。前提 P が真だろうと偽だろうと「P ならば P」は正しい。 -/
axiom imp_reflexive : P →ᵥ P

/-- 含意は推移的 -/
axiom imp_transitive (hpq : P →ᵥ Q) (hqr : Q →ᵥ R) : P →ᵥ R

/-- モーダスポネンス。「P ならば Q」は、P が正しければ Q が成り立つことを意味する。 -/
axiom imp_elim (hpq : P →ᵥ Q) (hP : P) : Q

/-- 結論が無条件に正しいなら、仮定をつけても正しい -/
axiom imp_intro (hQ : Q) : P →ᵥ Q

/-- ある前提から `Q` と `R` が導出できるなら、`Q ∧ R` も導出できる -/
axiom intro_and (hpq : P →ᵥ Q) (hpr : P →ᵥ R) : P →ᵥ (Q ∧ R)

/-- ある前提から `Q ∧ R` が導出できるなら、`Q` も導出できる -/
axiom elim_and_left (h : P →ᵥ (Q ∧ R)) : P →ᵥ Q

/-- ある前提から `Q ∧ R` が導出できるなら、`R` も導出できる -/
axiom elim_and_right (h : P →ᵥ (Q ∧ R)) : P →ᵥ R

/-- ある前提から `Q` が導出できるなら、`Q ∨ R` が導出できる -/
axiom intro_or_left (h : P →ᵥ Q) : P →ᵥ (Q ∨ R)

/-- ある前提から `R` が導出できるなら、`Q ∨ R` が導出できる -/
axiom intro_or_right (h : P →ᵥ R) : P →ᵥ (Q ∨ R)

end Imp --#

/- ## 問題
以上の要請のもとで、`P →ᵥ Q` が `P → Q` に一致することが証明できます。

以下の `sorry` を埋めてみてください。ただし、以下のことに注意してください。

* 仮定した要請を全部使う必要はありません。
* 古典論理に限った話ではないので、排中律を使わずに証明してみてください。

-/

variable {P Q : Prop}

open Imp

/-- 上記の要請を満たす `→ᵥ` は通常の含意と一致する -/
theorem imp_valid {P Q : Prop} : (P →ᵥ Q) ↔ (P → Q) := by
  sorry

--#--
section
/- ## 選択原理を使用していないことを確認するコマンド -/

open Lean Elab Command

elab "#detect_classical " id:ident : command => do
  let constName ← liftCoreM <| realizeGlobalConstNoOverload id
  let axioms ← collectAxioms constName
  if axioms.isEmpty then
    logInfo m!"'{constName}' does not depend on any axioms"
    return ()
  let caxes := axioms.filter fun nm => Name.isPrefixOf `Classical nm
  if caxes.isEmpty then
    logInfo m!"'{constName}' is non-classical and depends on axioms: {axioms.toList}"
  else
    throwError m!"'{constName}' depends on classical axioms: {caxes.toList}"

end

-- 選択原理を使用していないことを確認
#detect_classical imp_valid
--#--
