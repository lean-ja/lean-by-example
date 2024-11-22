/-
# CoeSort
`CorSort` は [`Coe`](./Coe.md) と同じく型強制を定義するための型クラスですが、違いとして型宇宙(`Type` や `Prop` など、項が再び型であるような型)への変換を専門に行う点が挙げられます。
-/
import Mathlib.Data.Fintype.Basic -- `Fintype` を使うため

/-- 有限集合の圏 -/
structure FinCat where
  /-- 台集合 -/
  base : Type

  /-- 台集合が有限集合であるという性質 -/
  fin : Fintype base

/-- 要素が2つの集合。有限集合なので `FinCat` のオブジェクト。-/
def Two : FinCat := { base := Fin 2, fin := inferInstance }

-- `Two` は有限集合の圏のオブジェクトなので集合っぽいものであってほしいが、
-- `Two` の型は `FinCat` であって `Type` などの型宇宙ではないので、
-- `a : Two` という書き方ができない。
/--
error: type expected, got
  (Two : FinCat)
-/
#guard_msgs in #check ((1 : Fin 2) : Two)

-- `Two → Two` という書き方もできない。
-- `A → A` も `A` の型が `Type` などの型宇宙であることを要求する。
/--
error: type expected, got
  (Two : FinCat)
-/
#guard_msgs in #check (Two → Two)

-- 台集合はあくまで `Two.base` なので、
-- `.base` をつける必要がある。
#check ((1 : Fin 2) : Two.base)
#check (Two.base → Two.base)

section --#
/-- `FinCat` から `Type` への型強制。
`S : FinCat` を、`S.base : Type` に変換する。-/
local instance : CoeSort FinCat Type := ⟨fun S ↦ S.base⟩

-- 型強制があるのでこういう書き方ができる
#check ((1 : Fin 2) : Two)
#check Two → Two
end --#

/- ## Coe との違い

`Coe` で同様のコードを書いても、上記の `FinCat` の例はうまくいきません。-/
section --#

local instance : Coe FinCat Type := ⟨fun S ↦ S.base⟩

#guard_msgs (drop warning) in --#
#check_failure ((1 : Fin 2) : Two)
#guard_msgs (drop warning) in --#
#check_failure (Two → Two)

end --#
/- しかし、これは「`Coe` では型宇宙への変換は扱えないから」ではありません。`Coe` と `CoeSort` では型強制が呼ばれるタイミングが異なるからです。`Coe` は「ある型の**項**が期待される場所に、異なる型の項が来た時」にトリガーされますが、`CoeSort` は「**型**が期待される場所に型が来ていないとき」にトリガーされます。

実際、`Coe` を使っても `Type` への型強制は定義することができます。
-/
section --#

/-- 型を受け取ってゼロを返す関数 -/
def zero (_ : Type) : Nat := 0

/-- `Type` のラッパー -/
structure AltType where
  base : Type

def A : AltType := ⟨Nat⟩

-- `zero` は `Type` を期待しているのでエラーになる
#guard_msgs (drop warning) in --#
#check_failure zero A

/-- `AltType` を `Type` に型強制する -/
local instance : Coe AltType Type := ⟨fun S ↦ S.base⟩

-- 成功するようになった！
#check zero A

end --#
