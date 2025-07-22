/- # big step に応用するための aesop ラッパーを作る

`aesop` をカスタマイズして、`big_step` というタクティクを作成する。
-/
import Aesop

-- BigStepRules という名前のルールセットを登録する
declare_aesop_rule_sets [BigStepRules]

/-- `BigStep` 用の aesop ラッパー -/
macro "big_step" : tactic => do `(tactic| aesop (rule_sets := [BigStepRules]))

/-- `big_step` が使用した補題を生成する -/
macro "big_step?" : tactic => `(tactic| aesop? (rule_sets := [BigStepRules]))

open Lean Parser Category

-- macro "big_step" e:Aesop.rule_expr : attr =>
--   `(attr| aesop (rule_sets := [BigStepRules]) $e)

/-- `big_step` タクティク用のルールを追加する -/
macro attrKind:attrKind "add_big_step_rules" e:Aesop.rule_expr : command =>
  `(command| $attrKind:attrKind add_aesop_rules (rule_sets := [BigStepRules]) $e)
