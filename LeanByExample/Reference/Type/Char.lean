/- # Char
`Char` 型は、Unicode 文字を表します。二重引用符 `"` ではなくてシングルクォート `'` で囲んで表されます。
-/

-- Char はシングルクォートで囲む
#check ('a' : Char)
#check ("a" : String)

-- Unicode 文字を含む
#check ('あ' : Char)
#check ('∀' : Char)
#check ('∅' : Char)

/- `Char` は、以下のように [`structure`](../Declarative/Structure.md) として定義されています。 -/

--#--
-- Char の定義が変わっていないことを確認するためのコード
/--
info: structure Char : Type
number of parameters: 0
fields:
  Char.val : UInt32
  Char.valid : self.val.isValidChar
constructor:
  Char.mk (val : UInt32) (valid : val.isValidChar) : Char
-/
#guard_msgs in #print Char
--#--
namespace Hidden --#

structure Char where
  /-- Unicode スカラー値 -/
  val : UInt32

  /-- `val` が正しいコードポイントであること -/
  valid : val.isValidChar

end Hidden --#
/- したがって `Char.val` 関数によりコードポイントを取得することができます。-/

#guard 'a'.val = 97
#guard '⨅'.val = 10757
