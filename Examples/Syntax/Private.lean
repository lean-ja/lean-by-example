/- # private
`private` は，その定義があるファイルの中でだけ参照可能になるようにする修飾子です．他のファイルからはアクセス不能になります．

不安定なAPIなど，外部に公開したくないものに対して使うのが主な用途です．
-/
import Examples.Syntax.Protected
import Lean --#

-- protected の項で private を使わずに定義した内容にアクセスできる
#check Point.sub

-- private とマークした定義にはアクセスできない
#check_failure Point.private_sub

/- なお `private` コマンドでセクションや名前空間にスコープを制限することはできません．-/

namespace Hoge
  section
    -- private とマークした定義
    private def addOne (n : Nat) : Nat := n + 1
  end
end Hoge

open Hoge

-- アクセスできる
#check addOne

/- 以下の例 [^private] のように，変数のスコープを制限するようなセクションの変種を自作することは可能です． -/

open Lean Elab Command

elab "private section" ppLine cmd:command* ppLine "end private section": command => do
  let old ← get
  try
    for cmd in cmd do
      elabCommandTopLevel cmd
    throwAbortCommand
  finally
    set old

private section
  def foo := "hello!!"

  -- セクションの中なら当然アクセスできる
  #check foo
end private section

-- `foo` にアクセスできない
#check_failure foo

/- [^private]: Alex J. Best さんによる [Zulip Chat/lean4/private section](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/private.20section/near/418114975) での投稿を元にした例です. -/
