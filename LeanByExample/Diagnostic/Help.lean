/- # \#help

`#help` は、ドキュメントを確認するためのコマンドです。以下のような機能があります。

* `#help tactic` で全タクティクのリストが見られます。
* `#help option` で全オプションのリストが見られます。オプションは、[`set_option`](../Declarative/SetOption.md) を実行することで切り替えられます。たとえば、`set_option warningAsError true` と書くと、warning(警告) がエラーとして扱われるようになります。
* `#help attr` で全 attribute のリストが見られます。たとえば `simp` という attribute なら、`@[simp] def foo := ...` という風にして登録できます。

* `#help command` で全コマンドのリストが見られます。
* `#help term` ですべての term syntax の一覧が見られます。

他にも機能がありますが、詳細は[Batteriesのドキュメント](https://leanprover-community.github.io/mathlib4_docs/Batteries/Tactic/HelpCmd.html)をご覧ください。
-/
import Batteries.Tactic.HelpCmd

-- 以下のコマンドで全 tactic のリストが見られます
#help tactic

-- 全 attribute のリストを見るには次のコマンドです
#help attr

-- 全コマンドのリストを見るには次のコマンドが使えます
#help command
