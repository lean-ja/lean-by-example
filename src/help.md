# help

`#help` は，ドキュメントを確認するためのコマンドです．

* `#help option` で全オプションのリストが見られます．オプションは，`set_option` を実行することで切り替えられます．たとえば，`set_option warningAsError true` と書くと，warning(警告) がエラーとして扱われるようになります．

* `#help attr` で全 attribute のリストが見られます．たとえば `simp` という attribute なら，`@[simp] def foo := ...` という風にして登録できます．

* `#help command` で全コマンドのリストが見られます．

* `#help term` ですべての term syntax の一覧が見られます．

他にも機能がありますが，詳細は Mathlib の定義ファイルをご覧ください．

```lean
{{#include ../Examples/Help.lean}}
```