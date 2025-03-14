/- # register_option

`register_option` は、オプションを自作するためのコマンドです。自作したオプションは [`set_option`](#{root}/Declarative/SetOption.md) から設定できるようになります。

```admonish warning title="注意"
このページの内容は <i class="fa fa-play"></i> ボタンから Lean 4 Web で実行することができません。
```

たとえば、`RegisterOptionLib.lean` というファイルを作成して、以下のように記述したとします。

{{#include ./RegisterOptionLib.md}}

このファイルを読み込めば、`greeting` というオプションを使用することができます。たとえば、以下のように使用することができます。
-/
import LeanByExample.Declarative.RegisterOptionLib

open Lean in

elab "#greet" : command => do
  let opts ← getOptions
  logInfo s!"greeting : {opts.get greeting.name greeting.defValue}"

-- デフォルト値が表示される
/-⋆-//-- info: greeting : Hello World -/
#guard_msgs in --#
#greet

-- オプションを設定すると
set_option greeting "Hi there"

-- 表示も変更される
/-⋆-//-- info: greeting : Hi there -/
#guard_msgs in --#
#greet
