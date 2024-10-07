/- # linter.flexible

`linter.flexible` オプションは、ライブラリの変更に対して頑強な証明を作るためのリンターの有効/無効を切り替えます。

## 背景

証明を書く際のベストプラクティスとして、[`simp`](#{root}/Reference/Tactic/Simp.md) タクティクのような柔軟性のあるタクティクは、証明の末尾以外で使わないほうがよいということが知られています。[^non-terminal-simp] `simp` タクティクはどういう補題が `[simp]` 属性で登録されているかに応じて挙動が変わるため、Mathlib に新たな`simp` 補題が追加されたり、あるいは削除されたりするたびに挙動が変わってしまうことがその理由です。

たとえば、以下のような証明を考えてみます。
-/
import Mathlib.Tactic --#

section --#
set_option linter.flexible false --#

opaque foo : Nat
opaque bar : Nat

/-- `foo` と `bar` が等しいという定理 -/
axiom foo_eq_bar : foo = bar

example {P : Nat → Prop} (hbar : P bar) : True ∧ (P foo) := by
  simp
  rw [foo_eq_bar]
  assumption

/- ここで、定理 `foo_eq_bar` は今のところ `[simp]` 属性が与えられていませんが、与えられると `rw` タクティクが失敗するようになります。-/

attribute [simp] foo_eq_bar

example {P : Nat → Prop} (hbar : P bar) : True ∧ (P foo) := by
  -- 元々はゴールを `P foo` に変えていた
  simp

  -- ゴールが変わってしまった
  guard_target =ₛ P bar

  -- `rw` タクティクが失敗するようになった
  fail_if_success rw [foo_eq_bar]

  assumption

end --#
/- ここで問題は、`[simp]` 属性が与えられる前の証明において、`simp` タクティクがゴールをどのように変えていたのかわからないということです。言い換えると、元々の証明の意図がわからないということです。それがわかっていれば、ライブラリの変更に合わせて証明を修正するのが少しは容易になります。

これは `simp` が柔軟(flexible)なタクティクであることの弊害で、対策として次のような方法が知られています。

* 証明末でしか `simp` タクティクを使わない。証明末であれば、「壊れる前の証明において `simp` が何を行っていたか」はつねに「残りのゴールを閉じる」であり明確で、ライブラリの変更があってもどう修正すればいいかがわかりやすいからです。
* [`have`](#{root}/Reference/Tactic/Have.md) タクティクや [`suffices`](#{root}/Reference/Tactic/Suffices.md) タクティクを使って証明末そのものを増やす。
* `simp only` 構文を使って、ライブラリ側に変更があっても `simp` タクティクの挙動が変わらないようにする。
* `simpa` タクティクのような、ゴールを閉じなければならないという制約を持つタクティクで書き換える。
-/
/- ## このリンタについて
このリンタを有効にすると、上記のようなライブラリの変更に対して脆弱な証明を自動で検出して、警告を出してくれます。
-/
section --#

-- 技術的な理由で、一時的に flexible tactic リンタを無効にしている --#
set_option linter.flexible false --#

/--
warning: 'simp' is a flexible tactic modifying '⊢'…
note: this linter can be disabled with `set_option linter.flexible false`
-/
#guard_msgs (warning) in
  -- 技術的な理由で、`#guard_msgs` のスコープ内でリンタを有効にしている
  set_option linter.flexible true in

  example {n m : Nat} (h : n = m) : True ∧ (n = m) := by
    simp
    exact h

example {n m : Nat} (h : n = m) : True ∧ (n = m) := by
  -- 書き換えると警告が消える
  simpa

/- [^non-terminal-simp]: <https://leanprover-community.github.io/extras/simp.html#non-terminal-simps> を参照のこと。-/

end --#
