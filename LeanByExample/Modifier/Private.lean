/- # private
`private` は、その定義があるファイルの中でだけ参照可能になるようにする修飾子です。他のファイルからはアクセス不能になります。不安定なAPIなど、外部に公開したくないものに対して使うのが主な用途です。

```admonish warning title="注意"
このページの内容は <i class="fa fa-play"></i> ボタンから Lean 4 Web で実行することができません。
```

たとえば、以下のように書かれているファイル `PrivateLib.lean` があったとしましょう。

{{#include ./PrivateLib.md}}

このとき、モジュール `PrivateLib` を読み込んでいるファイルからは、`protected` で修飾された名前はアクセス可能ですが、`private` で修飾された名前はアクセスできません。
-/
import LeanByExample.Modifier.PrivateLib -- private が使用されているモジュールをインポート
import Batteries.Tactic.OpenPrivate --#
import Lean --#

-- private を使わずに定義した内容にはアクセスできる
#check Point.sub

-- private とマークした定義にはアクセスできない
#check_failure Point.private_sub

/- なお `private` コマンドで定義した名前は、同じファイル内であればそのセクションや名前空間を出ても普通にアクセスすることができます。特に、`private` は [`protected`](#{root}/Modifier/Protected.md) の効果を持ちません。-/

namespace Hoge
  section
    -- private とマークした定義
    private def addOne (n : Nat) : Nat := n + 1

  end
end Hoge

open Hoge

-- 外からでもアクセスできる
#check addOne

/- ## 補足: `private`で隠された定義に一時的にアクセスする

`private` で隠された定義にアクセスする方法はあります。手軽なのは、`open private` コマンドを使う方法です。
-/

section
  -- 最初はアクセスできない
  #check_failure Point.private_sub

  -- `open private` コマンドを使用する
  open private Point.private_sub from LeanByExample.Modifier.PrivateLib

  -- アクセスできるようになった
  #check Point.private_sub
end
