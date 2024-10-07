/- # apply

`apply` は含意 `→` をゴールに適用するタクティクです。ゴールが `⊢ Q` で、ローカルコンテキストに `h : P → Q` があるときに、`apply h` を実行するとゴールが `⊢ P` に書き換わります。

「十分条件でゴールを置き換える」タクティクであると言えますが、十分条件がローカルコンテキストに存在しない場合は [`suffices`](./Suffices.md) の使用も検討してください。
-/
variable (P Q : Prop)

/-- `P → Q` かつ `P` ならば `Q` -/
example (h : P → Q) (hP : P) : Q := by
  apply h

  -- ゴールが `P` に変わっている
  show P

  exact hP

/- 注意点として、`h : P → Q` は `P` の証明を受け取って `Q` の証明を返す関数でもあるので、上記の例は `apply` を使わずに `exact h hP` で閉じることもできます。-/

example (h : P → Q) (hP : P) : Q := by
  exact h hP

/- さらに [`exact`](./Exact.md) の代わりに `apply` を使うこともできます。-/

example (h : P → Q) (hP : P) : Q := by
  apply h hP

/- また、Lean では否定 `¬ P` は `P → False` として実装されているため、ゴールが `⊢ False` であるときに `hn : ¬P` に対して `apply hn` とするとゴールが `⊢ P` に書き換わります。 -/

-- P の否定は、「P を仮定すると矛盾する」ということに等しい
example : (¬ P) = (P → False) := by rfl

example (hn : ¬ P) (hP : P) : False := by
  apply hn
  show P
  exact hP

/- ## 補足
一般に、`apply` は関数適用を逆算するタクティクです。手元に関数 `f : A → B` があって型 `B` の型を作りたいとき、`A` の項を構成すれば `f` に適用することで `B` の項が得られる…といった推論を行います。
-/

-- 関数をタクティクを使用して構成する例
def apply {α β : Type} (f : α → β) (a : α) : β := by
  apply f
  exact a
