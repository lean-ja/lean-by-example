import Lean

namespace HashSet

open Std

variable {α : Type} [BEq α] [Hashable α]
variable {β : Type} [BEq β] [Hashable β]

/--
HashSet.map がなぜ標準ライブラリにないのか考えていたが、
HashSet に対しては、map は自然な操作ではないのではないか？
原理や内部実装を考えてみればわかるかもしれない。

考えられる理由：
* `f`が単射だとは限らないので、`f`で送った後で重複が発生する可能性がある。
* `HashMap`を使って`HashSet`は実装されているので、自然な操作とは考えにくい。
-/
def map (f : α → β) (s : HashSet α) : HashSet β :=
  s.toList.map f |> HashSet.ofList

end HashSet
