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

/- タグに対する基本的な操作である、「タグが付与されている宣言をすべて集める」という操作をする例も挙げておきましょう。 -/
section

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

end

/- さらに応用として、「`[my_tag]` 属性が付与された定理を順に `apply` してゴールを閉じるタクティク」を自作する例も挙げておきます。 -/

@[my_tag]
theorem testThm (P Q : Prop) : P → Q → P ∧ Q := by
  simp_all

open Lean Elab Tactic in

/-- `@[my_tag]`タグが付与された定理をひたすら順に`apply`するタクティク -/
elab "apply_my_tagged" : tactic => do
  let taggedDecls ← listAllTagged myTagAttribute
  if taggedDecls.isEmpty then
    throwError "`[my_tag]`が付与された定理はありません。"
  for decl in taggedDecls do
    let declStx : TSyntax `term := mkIdent decl
    try
      evalTactic <| ← `(tactic| apply $declStx)

      -- 成功したら終了する
      return ()
    catch _ =>
      -- 失敗したら単に次の候補に進む
      pure ()
  throwError "ゴールを閉じることができませんでした。"

example (P Q : Prop) : P → Q → P ∧ Q := by
  apply_my_tagged
