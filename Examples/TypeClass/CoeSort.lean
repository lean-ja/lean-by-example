/-
# CoeSort
`CorSort` は [`Coe`](./Coe.md) と同じく型強制を定義するための型クラスですが、型宇宙(`Type` や `Prop` など、項が再び型であるような型)への変換を行う点が異なります。
-/
import Mathlib.Data.Fintype.Basic -- `Fintype` を使うため
namespace CoeSort --#

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

/- `Coe` で同様のコードを書いても、うまくいかないことに注意してください。-/

local instance : Coe FinCat Type := ⟨fun S ↦ S.base⟩

#check_failure ((1 : Fin 2) : Two)
#check_failure (Two → Two)

end CoeSort --#
