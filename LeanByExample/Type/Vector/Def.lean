--#--
/--
info: structure Vector.{u} (α : Type u) (n : Nat) : Type u
number of parameters: 2
fields:
  Vector.toArray : Array α
  Vector.size_toArray : self.toArray.size = n
constructor:
  Vector.mk.{u} {α : Type u} {n : Nat} (toArray : Array α) (size_toArray : toArray.size = n) : Vector α n
-/
#guard_msgs in #print Vector
--#--
namespace Hidden --#

/-- `Vector α n` はサイズが `n` であるような `Array α` -/
structure Vector.{u} (α : Type u) (n : Nat) where
  /-- 地の配列 -/
  toArray : Array α
  /-- 配列のサイズ -/
  size_toArray : toArray.size = n
deriving Repr, DecidableEq

end Hidden --#
