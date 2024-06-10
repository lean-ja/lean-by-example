/- # noncomputable
`noncomputable` は，宣言された関数が計算可能でないことを Lean に伝えるために使われます．

Lean は，`def` で定義された関数はすべて計算可能であると想定しています．したがって，計算可能でない関数を定義すると，エラーが発生します．

計算可能でない関数が生じるのは，選択原理 `Classical.choice` を使用したときです．選択原理は，型が「空ではない」という証明だけから，その型の項を魔法のように構成できると主張している公理です．空ではないという情報から具体的な項の情報は得られないため，選択原理を使用した関数は計算不能になります．
-/

variable {X Y : Type}

-- 写像 `f : X → Y` が全射であること
def Surjective (f : X → Y) : Prop := ∀ y, ∃ x, f x = y

-- 全射な関数の逆写像を構成する
-- しかし，全射という情報だけからは逆写像を具体的に作ることはできないので，
-- 計算不能になりエラーになってしまう
/--
error: failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'Classical.choice', and it does not have executable code
-/
#guard_msgs in def inverse' (f : X → Y) (hf : Surjective f) : Y → X := by
  -- `y : Y` が与えられたとする
  intro y

  -- `f` は全射なので `{x // f x = y}` は空ではない
  have : Nonempty {x // f x = y} := by
    let ⟨x, hx⟩ := hf y
    exact ⟨⟨x, hx⟩⟩

  -- 選択原理を用いて，`f x = y` なる `x : X` を構成する
  have x := Classical.choice this
  exact x.val

-- `noncomputable` という修飾子を付ければ，エラーは回避できる
noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
  intro y

  have : Nonempty {x // f x = y} := by
    let ⟨x, hx⟩ := hf y
    exact ⟨⟨x, hx⟩⟩

  have x := Classical.choice this
  exact x.val

/- `noncomputable` とマークされた式を含む式は文字通り評価不能になり，`#eval` に渡すことができなくなります．-/

-- 補助として `id` という恒等写像が全射であることを示しておく
theorem id_surjective : Surjective (id : Nat → Nat) := by
  intro y
  exists y

-- `id` の逆写像を構成する
noncomputable def id_inverse := inverse (id : Nat → Nat) id_surjective

-- 逆写像の `3` での値を評価しようとするとエラーになる
/--
error: failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'id_inverse', and it does not have executable code
-/
#guard_msgs in #eval id_inverse 3
