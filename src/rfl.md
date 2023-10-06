# rfl

needs: `import Mathlib.Tactic.Relation.Rfl`

named after: 反射律(reflexivity)

`rfl` は，`refl attribute` の付けられた定理を用いて関係の反射性を示すタクティクです．

```lean
{{#include ../Examples/Rfl/Rfl.lean:first}}
```

`@[refl]` で登録された定理を用いるので，追加でライブラリを import することにより示すことができる命題が増えます．

```lean
{{#include ../Examples/Rfl/Rfl.lean:nat}}
```

## 補足

実は `Mathlib.Tactic.Relation.Rfl` を import するかどうかにより，内部で呼び出されるタクティクが変わります．

* `Mathlib.Tactic.Relation.Rfl` ありなら [Lean.MVarId.rfl](https://leanprover-community.github.io/mathlib4_docs//Mathlib/Tactic/Relation/Rfl.html#Lean.MVarId.rfl) が，
* なしなら [Lean.MVarId.refl](https://leanprover-community.github.io/mathlib4_docs//Lean/Meta/Tactic/Refl.html#Lean.MVarId.refl) が

それぞれ参照されます．後者は `@[refl]` が付けられた一般の関係の反射性にアクセスできず，等号 `=` の反射性しか使うことができません．

後者の場合 `rfl` は，単に定義から等しいものが等しいことを示すタクティクになります．

```lean
{{#include ../Examples/Rfl/Refl.lean}}
```
