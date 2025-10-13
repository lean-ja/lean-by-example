/- # register_simp_attr

`register_simp_attr` は、[`simp`](#{root}/Tactic/Simp.md) タクティクで使うルールセットとタグを登録することができるコマンドで、`simp` ラッパとして新しいタクティクを作るのに使うことができます。

```admonish warning title="注意"
このページの内容は <i class="fa fa-play"></i> ボタンから Lean 4 Web で実行することができません。
```

## 使用例

以下では、型クラスによって導入される記法を定義に展開するタクティクを自作する例を示します。

このコマンドは属性タグを作るので、まず別のファイルを作って以下のように書き込みます。ファイル名は何でも良いのですが、仮に `RegisterSimpAttr/Lib.lean` であるとします。

{{#include ./RegisterSimpAttr/Lib.md}}

その後、このファイルをインポートすれば `@[notation_simp]` タグとルールセットが利用可能になります。以下のように、[`macro_rules`](#{root}/Declarative/MacroRules.md) コマンドを使用すれば `simp` ラッパを作成することができます。
-/
import LeanByExample.Declarative.RegisterSimpAttr.Lib -- インポートで有効になる

section
  open Lean Meta Parser.Tactic Elab.Tactic

  /-- `+`や`≤`など、演算子や記法を定義に展開する -/
  syntax (name := notation_simp_stx) "notation_simp" (simpArgs)? (location)? : tactic

  macro_rules
  | `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
    let args := simpArgs.map (·.getElems) |>.getD #[]
    `(tactic| simp only [notation_simp, $args,*] $[at $location]?)
end
/- これで、たとえば以下のように使用することができます。 -/

example {n m : Nat} (h : n < m) : n + 1 ≤ m := by
  -- notation_simp を使わない場合の方法。
  -- これを `(· < ·)` を展開したいときに毎回書く。
  dsimp [(· < ·), Nat.lt] at h
  assumption

@[notation_simp]
theorem Nat.lt_def (n m : Nat) : n < m ↔ (n + 1) ≤ m := by rfl

example {n m : Nat} (h : n < m) : n + 1 ≤ m := by
  -- これだけで展開が行えるようになった！
  notation_simp at h
  assumption

/- `notation_simp?` タクティクも自作するには、次のようにすればできます。 -/
section
  open Lean Meta Parser.Tactic Elab.Tactic

  @[inherit_doc notation_simp_stx]
  syntax (name := notation_simp?) "notation_simp?" (simpArgs)? (location)? : tactic

  macro_rules
  | `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
    let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)
end

/-⋆-//--
info: Try this:
  simp only [Nat.lt_def] at h
-/
#guard_msgs in --#
example {n m : Nat} (h : n < m) : n + 1 ≤ m := by
  notation_simp? at h
  assumption
