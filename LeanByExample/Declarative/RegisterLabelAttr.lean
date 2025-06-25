/- # register_label_attr

`register_label_attr` コマンドを使用すると、タグ属性を定義することができます。

```admonish warning title="注意"
このページの内容は <i class="fa fa-play"></i> ボタンから Lean 4 Web で実行することができません。
```

## 使用例

タグ属性を作るシンプルな例を示しましょう。

まず、以下のような内容のファイルを作成します。仮に `RegisterLabelAttrLib.lean` というファイル名だとします。

{{#include ./RegisterLabelAttrLib.md}}

これで、このファイルを `import` しているファイルの中で `@[my_tag]` タグを使用することができます。
-/
import LeanByExample.Declarative.RegisterLabelAttrLib

@[my_tag]
def greet := "Hello, world!"

/- もちろんタグとしてだけでなく普通の属性としても使用可能です。 -/

def foo := 42

attribute [my_tag] foo

/- タグに対する基本的な操作である、「タグが付与されている宣言をすべて集める」という操作は`Lean.labelled`関数で実行することができます。 -/

/-⋆-//-- info: #[`greet, `foo] -/
#guard_msgs in --#
#eval Lean.labelled `my_tag

/- さらに応用として、「`[my_tag]` 属性が付与された定理を順に `apply` してゴールを閉じるタクティク」を自作する例も挙げておきます。 -/

open Lean Elab Tactic

elab "apply_my_tagged" : tactic => do
  let taggedDecls ← labelled `my_tag
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

@[my_tag]
theorem testThm (P Q : Prop) : P → Q → P ∧ Q := by
  simp_all

example (P Q : Prop) : P → Q → P ∧ Q := by
  apply_my_tagged
