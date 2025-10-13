/- # declare_aesop_rule_sets

`declare_aesop_rule_sets` コマンドは、[`aesop`](#{root}/Tactic/Aesop.md) タクティクで使用させるための特定のルールセットを宣言します。

```admonish warning title="注意"
このページの内容は <i class="fa fa-play"></i> ボタンから Lean 4 Web で実行することができません。
```

## 基本的な使い方

`declare_aesop_rule_sets` で宣言されたルールセットは、宣言したそのファイルの中では有効になりません。`import` する必要があります。前提として以下の内容のファイルを `import` しているとしましょう。

{{#include ./DeclareAesopRuleSets/Lib.md}}

このとき、以下のように `aesop` の `rule_sets` に `HogeRules` を渡すことで、`HogeRules` に登録されたルールセットを使用することができます。
-/
import LeanByExample.Declarative.DeclareAesopRuleSets.Lib -- インポートで有効になる
import Mathlib.Tactic.Says --#

example : True := by
  aesop (rule_sets := [HogeRules])

/- ## タクティク作成

このコマンドの主な用途は、`aesop` をカスタマイズして `aesop` と同じように使えるタクティクを自作することです。特定のルールセットに対して登録されたルールは単に `aesop` を実行しただけでは適用されないので、用途ごとにタクティクを分けることができるという理屈です。

たとえば、[`macro`](./Macro.md) コマンドを使ったシンプルな方法で、`aesop` が持つデフォルトのルールセットはそのままに`aesop` をベースに新たに `hoge` というタクティクを作ることができます。
-/

/-- aesop ラッパー -/
macro "hoge" : tactic => do `(tactic| aesop (rule_sets := [HogeRules]))

example : True := by
  hoge

/- `aesop?` と同等の機能も、同じようにして実現することができます。-/

/-- `hoge` が使用したルールを生成する -/
macro "hoge?" : tactic => `(tactic| aesop? (rule_sets := [HogeRules]))

example : True := by
  hoge? says simp_all only

/- `hoge` タクティク用のルールを登録することもできます。

`[aesop]` 属性と同等の機能を持つ `[hoge]` 属性を作成したい場合は、たとえば次のようにします。-/

/-- `hoge` タクティク用のルールを追加する -/
macro "hoge" e:Aesop.rule_expr : attr =>
  `(attr| aesop (rule_sets := [HogeRules]) $e)

namespace Attr --#

/-- `True` を模して自作した命題 -/
inductive MyTrue : Prop where
  | intro

example : MyTrue := by
  -- 最初は証明できない
  fail_if_success hoge

  apply MyTrue.intro

attribute [local hoge safe constructors] MyTrue

example : MyTrue := by
  -- `hoge` で証明できるようになった！
  hoge

example : MyTrue := by
  -- 依然として `aesop` では証明できない
  fail_if_success aesop

  apply MyTrue.intro

end Attr --#

/- [`add_aesop_rules`](#{root}/Declarative/AddAesopRules.md) コマンドと同様の機能を持つ `add_hoge_rules` コマンドを作成したい場合は、たとえば次のようにします。-/

/-- `hoge` タクティク用のルールを追加する -/
macro attrKind:attrKind "add_hoge_rules" e:Aesop.rule_expr : command =>
  `(command| $attrKind:attrKind add_aesop_rules (rule_sets := [HogeRules]) $e)

namespace Command --#

/-- `True` を模して自作した命題 -/
inductive MyTrue : Prop where
  | intro

example : MyTrue := by
  -- 最初は証明できない
  fail_if_success hoge

  apply MyTrue.intro

-- `MyTrue` に関するルールを `hoge` に登録する
local add_hoge_rules safe constructors [MyTrue]

example : MyTrue := by
  -- `hoge` で証明できるようになった!
  hoge

example : MyTrue := by
  -- 依然として `aesop` では証明できない
  fail_if_success aesop

  apply MyTrue.intro

end Command --#
