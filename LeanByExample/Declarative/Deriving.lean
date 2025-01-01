/-
# deriving
`deriving` は、型クラスのインスタンスを自動的に生成します。

以下に示すように、`deriving instance C for T` とすると型 `T` に対して型クラス `C` のインスタンスを生成します。
-/
namespace Deriving --#

inductive Color : Type where
  | red
  | green
  | blue

-- 暗黙的に Repr インスタンスを生成しない
set_option eval.derive.repr false

-- `Repr` が定義されていないので `eval` できない
/--
error: could not synthesize a 'Repr' or 'ToString' instance for type
  Color
-/
#guard_msgs in #eval Color.red

-- インスタンス生成
deriving instance Repr for Color

-- `eval` できるようになった
#eval Color.red

/- ## deriving 句
対象の型の直後であれば、省略して `deriving C` だけ書けば十分です。-/

def StrList := List String deriving Inhabited

#check (default : StrList)

/- また複数の型クラスに対してインスタンスを生成するには、クラス名をカンマで続けます。 -/

structure People where
  name : String
  age : Nat
deriving Inhabited, Repr

-- 両方のインスタンスが生成されている
#eval (default : People)

/- ## よくあるエラー
なお、`deriving` で実装を生成できるのは、決まりきったやり方で実装できて、実装方法が指定されている型クラスのみです。実装方法が指定されていなければ使うことはできません。-/

/-- 自前で定義した型クラス -/
class Callable (α : Type) where
  call : α → String

/--
error: default handlers have not been implemented yet,
class: 'Deriving.Callable' types: [Deriving.People]
-/
#guard_msgs in deriving instance Callable for People

end Deriving --#
