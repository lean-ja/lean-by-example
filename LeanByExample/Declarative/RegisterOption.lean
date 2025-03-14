/- # register_option

`register_option` は、オプションを自作するためのコマンドです。自作したオプションは [`set_option`](#{root}/Declarative/SetOption.md) から設定できるようになります。

```admonish warning title="注意"
このページの内容は <i class="fa fa-play"></i> ボタンから Lean 4 Web で実行することができません。
```

## 使用例

### デモンストレーション

たとえば、`RegisterOptionLib.lean` というファイルを作成して、以下のように記述したとします。

{{#include ./RegisterOptionLib.md}}

このファイルを読み込めば、`greeting` というオプションを使用することができます。たとえば、以下のように使用することができます。
-/
import LeanByExample.Declarative.RegisterOptionDC --#
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

/- ### リンター自作

選択原理を証明の中で使用すると警告してくれるリンターを自作することができます。[^dc]
以下のように記述したファイルを読み込みます。

{{#include ./RegisterOptionDC.md}}

すると、次のように使用できます。
-/

set_option linter.detectClassical true

-- 選択原理を使用しているため警告が出る
/-⋆-//--
warning: 'prop_iff_neg_self₀' depends on 'Classical.choice'.

All axioms: [Classical.choice, propext, Quot.sound]

note: this linter can be disabled with `set_option linter.detectClassical false`
-/
#guard_msgs in --#
theorem prop_iff_neg_self₀ (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h
  by_cases hp : P
  · have : ¬ P := by
      rwa [h] at hp
    contradiction
  · have : ¬ ¬ P := by
      rwa [h] at hp
    contradiction

-- 選択原理に依存しない証明には警告が出ない
#guard_msgs (warning) in
  theorem prop_iff_neg_self₁ (P : Prop) : ¬ (P ↔ ¬ P) := by
    intro h
    have hnp : ¬ P := by
      intro hp
      have hnp : ¬ P := by
        rwa [h] at hp
      contradiction
    have hp : P := by
      have : ¬ ¬ P := by
        rwa [h] at hnp
      contradiction
    contradiction

/- [^dc]: この例は Lean 公式の Zulip の restricting axioms というトピックにおける、[Damiano Testa さんの投稿](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms/near/501743343)を参考にしています。 -/
