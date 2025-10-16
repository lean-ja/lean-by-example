import LeanByExample.Type.DerivingHandler.Lib

-- 最初はインスタンスがない
#check_failure ToUnit.toUnit true

-- `deriving` コマンドを使用
deriving instance ToUnit for Bool, Int, Char

-- インスタンスが生成された！
#guard ToUnit.toUnit true = ()
#guard ToUnit.toUnit (42 : Int) = ()
#guard ToUnit.toUnit 'a' = ()
