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

/- ## 符号位置
`Char` は、以下のように [`structure`](#{root}/Declarative/Structure.md) として定義されています。 -/

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

  /-- `val` が正しく Unicode の code point であること -/
  valid : val.isValidChar

end Hidden --#
/- したがって `Char.val` 関数により **符号位置(code point)** を取得することができます。-/

#guard 'a'.val = 97
#guard '⨅'.val = 10757

/- これを利用すると、たとえば「アルファベットを与えられた整数 `n` だけずらして暗号化する関数」を以下のように実装することができます。[^code] -/

/-- アルファベットのインデックス -/
structure Index where
  /-- 番号。`0`から`25`の数字 -/
  index : Nat
  /-- 小文字かどうか -/
  isLower : Bool
deriving Inhabited, DecidableEq


/-- アルファベットを`Index`に変換する -/
def Char.toIndex (c : Char) : Index :=
  if c.isLower then
    ⟨c.val - 'a'.val |>.toNat, true⟩
  else if c.isUpper then
    ⟨c.val - 'A'.val |>.toNat, false⟩
  else
    panic! s!"toIndex: input is {c}, which is not an alphabet"

#guard 'a'.toIndex = ⟨0, true⟩
#guard 'B'.toIndex = ⟨1, false⟩


/-- インデックスをアルファベットに変換する -/
def Char.ofIndex (i : Index) : Char :=
  if i.isLower then
    Char.ofNat ('a'.val.toNat + i.index)
  else
    Char.ofNat ('A'.val.toNat + i.index)

#guard Char.ofIndex ⟨0, true⟩ = 'a'
#guard Char.ofIndex ⟨1, false⟩ = 'B'


/-- アルファベットを`n`だけシフトする -/
def Char.shift (c : Char) (n : Int) : Char :=
  if c.isAlpha then
    let code := (c.toIndex.index + n) % 26 |>.toNat
    let index : Index := ⟨code, c.isLower⟩
    Char.ofIndex index
  else
    c

#guard Char.shift 'a' 3 = 'd'
#guard Char.shift 'z' 3 = 'c'
#guard Char.shift 'B' (-3) = 'Y'


/-- シーザー暗号の実装。文字列に登場する文字をシフトする。 -/
def String.encode (s : String) (n : Int) : String :=
  s.map (Char.shift · n)

#guard "I am a magician.".encode 3 = "L dp d pdjlfldq."
#guard "L dp d pdjlfldq.".encode (-3) = "I am a magician."

/- [^code]: この例は、Graham Hutton「プログラミングHaskell第２版」（ラムダノート）第５章を参考にしています。 -/
