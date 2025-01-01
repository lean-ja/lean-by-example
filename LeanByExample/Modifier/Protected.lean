/-
# protected
`protected` は、ある名前空間 `Hoge` にある定義 `foo` に対して、必ずフルネームの `Hoge.foo` でアクセスすることを強要するものです。
-/
section --#
structure Point where
  x : Nat
  y : Nat

namespace Point

  protected def sub (p q : Point) : Point :=
    { x := p.x - q.x, y := p.y - q.y }

  -- 名前空間の中にいても、短い名前ではアクセスできない
  #guard_msgs (drop warning) in --#
  #check_failure sub

  -- フルネームならアクセスできる
  #check Point.sub

end Point

open Point

-- 名前空間を開いていても、短い名前でアクセスできない
#guard_msgs (drop warning) in --#
#check_failure sub

-- フルネームならアクセスできる
#check Point.sub

end --#
/- ## protected を使う場面
環境の中に `Foo.bar` と `bar` が存在したとします。このとき名前空間 `Foo` の中にいた場合は、`Foo.bar` の方が優先されます。したがってルートにある方の `bar` は覆い隠され、アクセスしづらくなります。
-/

def Foo.bar := "hello"

def bar := "world"

namespace Foo

-- 単に bar と書くと Foo.bar が参照される
#guard bar = "hello"

-- ルートにある bar を参照することも _root_ を付ければ可能
#guard _root_.bar = "world"

end Foo

/- `Foo.baz` を `protected` として宣言しておけば、他の名前空間に影響を及ぼさなくなります。-/

protected def Foo.baz := "hello"

def baz := "world"

namespace Foo

-- 単に baz と書いたらルートの baz が参照される
#guard baz = "world"

end Foo

/- ## protected def 以外の用法

`def` コマンドに対してだけでなく、[`indudctive`](#{root}/Declarative/Inductive.md) コマンドで生成されるコンストラクタに対しても使用可能です。-/
section --#

/-- 2分木 -/
inductive BinTree (α : Type) where
  | empty : BinTree α
  | protected node : α → BinTree α → BinTree α → BinTree α

-- 名前空間を開く
open BinTree

-- 名前空間を開いているのに、
-- コンストラクタに短い名前でアクセスできない
#guard_msgs (drop warning) in --#
#check_failure node
#check BinTree.node

-- protected でない方は短い名前でアクセスできる
#check empty

end --#
/- また [`structure`](#{root}/Declarative/Structure.md) コマンドで生成されるアクセサ関数やコンストラクタに対しても使用可能です。 -/
section --#
structure Sample where
  -- コンストラクタも protected にできる
  protected mk ::

  bar : Nat
  protected hoge : String

open Sample

-- 名前空間を開いているので bar には短い名前でアクセスできる
#check bar

-- hoge には短い名前でアクセスできない
#guard_msgs (drop warning) in --#
#check_failure hoge

end --#
