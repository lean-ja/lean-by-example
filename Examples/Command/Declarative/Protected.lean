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

  -- private のテスト用の宣言
  private def private_sub := Point.sub

  -- 名前空間の中にいても、短い名前ではアクセスできない
  #check_failure sub

  -- フルネームならアクセスできる
  #check Point.sub

end Point

open Point

-- 名前空間を開いていても、短い名前でアクセスできない
#check_failure sub

-- フルネームならアクセスできる
#check Point.sub

end --#
/- ## protected def 以外の用法

`def` コマンドに対してだけでなく、[`indudctive`](./Inductive.md) コマンドで生成されるコンストラクタに対しても使用可能です。-/
section --#

/-- 2分木 -/
inductive BinTree (α : Type) where
  | empty : BinTree α
  | protected node : α → BinTree α → BinTree α → BinTree α

-- 名前空間を開く
open BinTree

-- 名前空間を開いているのに、
-- コンストラクタに短い名前でアクセスできない
#check_failure node
#check BinTree.node

-- protected でない方は短い名前でアクセスできる
#check empty

end --#
/- また [`structure`](./Structure.md) コマンドで生成されるアクセサ関数やコンストラクタに対しても使用可能です。  -/
section --#
structure Foo where
  -- コンストラクタも protected にできる
  protected mk ::

  bar : Nat
  protected baz : String

open Foo

-- 名前空間を開いているので bar には短い名前でアクセスできる
#check bar

-- baz には短い名前でアクセスできない
#check_failure baz

end --#
