/- # linter.flexible

`linter.flexible` オプションは、ライブラリの変更に対して頑強な証明を作るためのリンタの有効/無効を切り替えます。

## 背景

証明を書く際のベストプラクティスとして、[`simp`](#{root}/Tactic/Simp.md) タクティクのような柔軟性のあるタクティクは、証明の末尾以外で使わないほうがよいということが知られています。[^non-terminal-simp] `simp` タクティクはどういう補題が `[simp]` 属性で登録されているかに応じて挙動が変わるため、引用しているライブラリに `simp` 補題が新たに追加されたり、削除されたりするたびに挙動が変わってしまうためです。

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
/- ここで問題は、`simp` 補題が追加される前の証明において、元々 `simp` タクティクがゴールを何から何に変形していたのかわからないということです。この例では `foo_eq_bar` が追加されたことが分かっていますが、一般にはライブラリにどのような変更があったのかはすぐにわかることではありません。ライブラリの差分のことを知らなくても、証明が壊れる前の `simp` タクティクが何を行っていたか知る方法が必要です。

これは `simp` が柔軟(flexible)なタクティクであることが原因で、対策として次のような方法が知られています。

* 証明末でしか `simp` タクティクを使わない。証明末であれば、「壊れる前の証明において `simp` が何を行っていたか」は常に「残りのゴールを閉じる」であり明確で、ライブラリの変更があってもどう修正すればいいかがわかりやすいからです。
* [`have`](#{root}/Tactic/Have.md) タクティクや [`suffices`](#{root}/Tactic/Suffices.md) タクティクを使って証明末そのものを増やす。
* `simp only` 構文を使って、ライブラリ側に変更があっても `simp` タクティクの挙動が変わらないようにする。
* `simpa` タクティクのような、ゴールを閉じなければならないという制約を持つタクティクで書き換える。
-/
/- ## このリンタについて
このリンタを有効にすると、上記のようなライブラリの変更に対して脆弱な証明を自動で検出して、警告を出してくれます。
-/
section --#

set_option linter.flexible true

/-⋆-//--
warning: 'simp' is a flexible tactic modifying '⊢'…
note: this linter can be disabled with `set_option linter.flexible false`
-/
#guard_msgs (warning) in --#
example {n m : Nat} (h : n = m) : True ∧ (n = m) := by
  simp
  exact h

example {n m : Nat} (h : n = m) : True ∧ (n = m) := by
  -- 書き換えると警告が消える
  simpa

/- [^non-terminal-simp]: <https://leanprover-community.github.io/extras/simp.html#non-terminal-simps> を参照のこと。-/

end --#
