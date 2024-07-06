/-
# ToString
`ToString` は，文字列への変換を行う型クラスです．
-/
namespace ToString --#

structure Point (α : Type) where
  x : α
  y : α

def origin : Point Int := ⟨0, 0⟩

-- 文字列補完により文字列に変換しようとしても，
-- 最初はどう変換したらいいのかわからないのでエラーになる
#check_failure s!"{origin}"

/-- `ToString` のインスタンスを登録する -/
instance : ToString (Point Int) where
  toString p := s!"Point: ({p.x}, {p.y})"

-- これで文字列に変換できる
#eval s!"{origin}"

/- なお，`Repr` のインスタンスがないが，`ToString` のインスタンスはある状態で `#eval` しようとすると，`Repr` の代わりに `ToString` のインスタンスが使用されます．`Repr` のインスタンスを与えればそちらが優先して使用されます．-/

/-- info: Point: (0, 0) -/
#guard_msgs in --#
#eval origin

-- `Repr` のインスタンスを自動生成して登録する
-- 以降は，`#eval` 時には `Repr` のインスタンスが使用される
deriving instance Repr for Point

/-- info: { x := 0, y := 0 } -/
#guard_msgs in --#
#eval origin

end ToString --#
