/- # \#instances
`#instances` は、与えられた型クラスのインスタンスの完全なリストを出力するコマンドです。
-/
import Batteries.Tactic.Instances -- `#instances` コマンドを使うために必要

-- 内容が何もない例示のためだけの型クラス
class Hoge (α : Type) where
  hoge : Unit

-- `Nat` を `Hoge` のインスタンスにする
instance : Hoge Nat where
  hoge := ()

-- `Bool` を `Hoge` のインスタンスにする
instance : Hoge Bool where
  hoge := ()

-- 今登録した2つのインスタンスが表示される
/-⋆-//--
info: 2 instances:

instHogeBool : Hoge Bool
instHogeNat : Hoge Nat
-/
#guard_msgs in --#
#instances Hoge
