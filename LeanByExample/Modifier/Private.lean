/- # private
`private` は、その定義があるファイルの中でだけ参照可能になるようにする修飾子です。他のファイルからはアクセス不能になります。不安定なAPIなど、外部に公開したくないものに対して使うのが主な用途です。

たとえば、以下のように書かれているファイル `PrivateLib.lean` があったとしましょう。

{{#include ./PrivateLib.md}}

このとき、モジュール `PrivateLib` を読み込んでいるファイルからは、`protected` で修飾された名前はアクセス可能ですが、`private` で修飾された名前はアクセスできません。
-/
import LeanByExample.Modifier.PrivateLib -- private が使用されているモジュールをインポート
import Lean
namespace Private --#

-- private を使わずに定義した内容にはアクセスできる
#check Point.sub

-- private とマークした定義にはアクセスできない
#guard_msgs (drop warning) in --#
#check_failure Point.private_sub

/- なお `private` コマンドで定義した名前は、同じファイル内であればそのセクションや名前空間を出てもアクセスすることができます。-/

namespace Hoge
  section
    -- private とマークした定義
    private def addOne (n : Nat) : Nat := n + 1

  end
end Hoge

open Hoge

-- 外からでもアクセスできる
#check addOne

/- ## 舞台裏
`private` コマンドを用いて宣言した名前は、そのファイルの外部からはアクセス不能になるものの、そのファイル内部からは一見 `private` でない名前と同様に見えます。しかし、特定の名前が `private` であるか判定する関数は存在します。
-/

private def hoge := "hello"

def foo := "world"

-- 名前が private かどうか判定する関数
#check (Lean.isPrivateName : Lean.Name → Bool)

#guard Lean.isPrivateName ``hoge

#guard Lean.isPrivateName ``foo = false

end Private --#
