/-
# protected

`protected` は、ある名前空間 `Hoge` にある定義 `foo` に対して、短い名前 `foo` でアクセスすることを禁止するものです。
-/

namespace Playground

  /-- protected が付いていない定義 -/
  def ordianal_hoge := "hoge"

  /-- protected が付いている定義 -/
  protected def protected_hoge := "hoge"

end Playground

namespace Playground

  -- 名前空間の中なので、短い名前でアクセスできる
  -- (通常の挙動)
  #check ordianal_hoge

  -- 名前空間を開いているが、短い名前ではアクセスできない
  #check_failure protected_hoge

  -- 名前空間名を補えばアクセスできる
  #check Playground.protected_hoge

end Playground

section
  open Playground

  -- 名前空間を `open` しているので、
  -- 短い名前でアクセスできる（通常の挙動）
  #check ordianal_hoge

  -- 名前空間を `open` しているが、短い名前ではアクセスできない
  #check_failure protected_hoge
end

/- ## 構文

`def` コマンドに対してだけでなく、[`indudctive`](#{root}/Declarative/Inductive.md) コマンドで生成されるコンストラクタに対しても使用可能です。-/

/-- 2分木 -/
inductive BinTree (α : Type) where
  | empty : BinTree α
  | protected node : α → BinTree α → BinTree α → BinTree α

section

  -- 名前空間を開く
  open BinTree

  -- 名前空間を open しているが、
  -- コンストラクタに短い名前でアクセスできない
  #check_failure node
  #check BinTree.node

  -- protected でない方は短い名前でアクセスできる
  #check empty

end
/-
また [`structure`](#{root}/Declarative/Structure.md) コマンドで生成されるアクセサ関数やコンストラクタに対しても使用可能です。
-/
structure Sample where
  -- コンストラクタも protected にできる
  protected mk ::

  bar : Nat
  protected hoge : String

section

  open Sample

  -- 名前空間を open しているので bar には短い名前でアクセスできる
  #check bar

  -- hoge には短い名前でアクセスできない
  #check_failure hoge

end
/- ## 用途

機能から想像がつくと思いますが、`protected` は混同を避けるために使用されます。

`protected` を使うべき典型的な状況は、型クラスのメソッドが [`export`](#{root}/Declarative/Export.md) されている場合です。
-/

/-- 文字列をパースして `α` 型の項を得る方法を提供する型クラス -/
class OfString (α : Type) where
  ofString : String → Option α

export OfString (ofString)

/-
型クラスのメソッドを用意するときに、関数名は往々にしてそのメソッドと同じ名前にするので、紛らわしさが生じます。
-/

namespace Bool

  -- `Bool` 名前空間の中にいると、
  -- `Bool.ofString` と `OfString.ofString` が紛らわしい
  def ofString (s : String) : Option Bool :=
    match s with
    | "true" => some true
    | "false" => some false
    | _ => none

  instance : OfString Bool where
    ofString := ofString

  -- `Bool.ofString` の方を指している
  /-- info: Bool.ofString (s : String) : Option Bool -/
  #guard_msgs in --#
  #check ofString

end Bool

-- `OfString.ofString` の方を指している
/-- info: OfString.ofString {α : Type} [self : OfString α] : String → Option α -/
#guard_msgs in --#
#check ofString

/-
`protected` を使用すると、「型クラスのメソッドの具体的な実装の方を指したいときは、明示的に名前空間を補う」というルールにできるので、紛らわしさが改善されます。
-/

namespace Unit

  protected def ofString (s : String) : Option Unit :=
    match s with
    | "()" => some ()
    | _ => none

  instance : OfString Unit where
    ofString := Unit.ofString

  -- `OfString.ofString` の方を指している
  /-- info: OfString.ofString {α : Type} [self : OfString α] : String → Option α -/
  #guard_msgs in --#
  #check ofString

end Unit
