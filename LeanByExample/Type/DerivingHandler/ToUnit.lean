/-- `Unit`への変換方法を与える自明な型クラス -/
class ToUnit (α : Type) where
  toUnit : α → Unit

/-- `Nat`における `ToUnit` のインスタンス -/
instance : ToUnit Nat where
  toUnit _ := ()

/-- `String`における `ToUnit` のインスタンス -/
instance : ToUnit String where
  toUnit _ := ()

#guard ToUnit.toUnit 42 = ()
#guard ToUnit.toUnit "hello" = ()
