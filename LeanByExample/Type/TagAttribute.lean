/- # TagAttribute

`Lean.TagAttribute` の項は、タグとして使用可能な属性です。

```admonish warning title="注意"
このページの内容は <i class="fa fa-play"></i> ボタンから Lean 4 Web で実行することができません。
```

## 使用例

`TagAttribute` の項を使用して、タグ属性を作るシンプルな例を示しましょう。

まず、以下のような内容のファイルを作成します。仮に `TagAttributeLib.lean` というファイル名だとします。

{{#include ./TagAttributeLib.md}}

これで、このファイルを `import` しているファイルの中で `@[my_tag]` タグを使用することができます。
-/
import LeanByExample.Type.TagAttributeLib

@[my_tag] def hello := "hello, Lean!"

/- もちろんタグとしてだけでなく普通の属性としても使用可能です。 -/

def foo := "foo"

attribute [my_tag] foo

/- タグに対する基本的な操作である、「タグが付与されている宣言をすべて集める」という操作もできます。 -/

open Lean

/-- `[tagAttr]`属性が付与されているものをリストアップする -/
def listAllTagged (tagAttr : TagAttribute) : MetaM (List Name) := do
  let env ← getEnv
  let taggedDecls := tagAttr.ext.getState env
  return taggedDecls.toList

/-⋆-//-- info: `[my_tag]`が付与されているもの: [hello, foo] -/
#guard_msgs in --#
run_meta
  let tagged ← listAllTagged myTagAttribute
  logInfo m!"`[my_tag]`が付与されているもの: {tagged}"
