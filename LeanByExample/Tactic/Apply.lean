/- # apply

`apply` は含意 `→` をゴールに適用するタクティクです。ゴールが `⊢ Q` で、ローカルコンテキストに `h : P → Q` があるときに、`apply h` を実行するとゴールが `⊢ P` に書き換わります。
-/
variable (P Q : Prop)

/-- `P → Q` かつ `P` ならば `Q` -/
example (h : P → Q) (hP : P) : Q := by
  apply h

  -- ゴールが `P` に変わっている
  show P

  exact hP

/- 「十分条件でゴールを置き換える」タクティクであると言えますが、十分条件がローカルコンテキストに存在しない場合は [`suffices`](./Suffices.md) の使用も検討してください。-/

/- ## 特殊な用途

### 仮説から否定を消去する
Lean では否定 `¬ P` は `P → False` として実装されているため、ゴールが `⊢ False` であるときに `hn : ¬P` に対して `apply hn` とするとゴールを `⊢ P` に書き換えることができます。
-/

-- P の否定は、「P を仮定すると矛盾する」ということに等しい
example : (¬ P) = (P → False) := by rfl

example (hn : ¬ P) (hP : P) : False := by
  apply hn
  show P
  exact hP

/- ### exact の強力版として

[`exact`](./Exact.md) の代わりに `apply` を使うこともできます。-/

example (hP : P) : P := by
  apply hP

example (h : P → Q) (hP : P) : Q := by
  apply h hP

/- また仮定に全称命題の証明 `h : ∀ a, P a` があってゴールが `P a` であるとき、`exact h` は失敗しますが `apply h` であれば成功します。これは「`exact` では通りそうで通らないが `apply` では通る例」であると言えるかもしれません。-/

variable {α : Type}

example (a : α) (P : α → Prop) (h : ∀ a, P a) : P a := by
  -- `exact h` は失敗する
  fail_if_success exact h

  apply h

/- ## 舞台裏
一般に、`apply` は関数適用を逆算するタクティクです。手元に関数 `f : A → B` があって型 `B` の型を作りたいとき、`A` の項を構成すれば `f` に適用することで `B` の項が得られる…といった推論を行います。
-/

-- 関数をタクティクを使用して構成する例
def apply {α β : Type} (f : α → β) (a : α) : β := by
  apply f
  exact a
