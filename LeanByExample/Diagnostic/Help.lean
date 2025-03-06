/- # \#help

`#help` は、ドキュメントを確認するためのコマンドです。以下のような機能があります。

* `#help tactic` で全タクティクのリストが見られます。
* `#help option` で全オプションのリストが見られます。オプションは、[`set_option`](#{root}/Declarative/SetOption.md) を実行することで切り替えることができます。
* `#help attr` で全[属性(attribute)](#{root}/Declarative/Attribute.md)のリストが見られます。
* `#help command` で全コマンドのリストが見られます。
* `#help term` ですべての term syntax の一覧が見られます。

他にも機能がありますが、詳細は[Batteriesのドキュメント](https://leanprover-community.github.io/mathlib4_docs/Batteries/Tactic/HelpCmd.html)をご覧ください。

```admonish info title=""
[Mathlib4 Help](https://seasawher.github.io/mathlib4-help/) で `#help` コマンドの出力結果を見ることができます。
```
-/
import Batteries.Tactic.HelpCmd

-- 以下のコマンドで全 tactic のリストが見られます
#help tactic

-- 全 attribute のリストを見るには次のコマンドです
#help attr

-- 全コマンドのリストを見るには次のコマンドが使えます
#help command
