/- # postfix

`postfix` は、後置記法を定義するコマンドです。
-/
import Lean --#

/-- 階乗 -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- 後置記法を定義する
postfix:200 "!" => factorial

-- 定義した記法が使える
#guard 5! = 120

/- ## 舞台裏
`postfix` は [`notation`](./Notation.md) コマンドに展開されるマクロとして実装されています。
-/
section
  open Lean

  /-- `#expand` の入力に渡すための構文カテゴリ -/
  syntax macro_stx := command <|> tactic <|> term

  /-- マクロを展開するコマンド -/
  elab "#expand " "(" stx:macro_stx ")" : command => do
    let t : Syntax :=
      match stx.raw with
      | .node _ _ #[t] => t
      | _ => stx.raw
    match ← Elab.liftMacroM <| Macro.expandMacro? t with
    | none => logInfo m!"Not a macro"
    | some t => logInfo m!"{t}"
end

/-- info: notation:200 arg✝:200 "!" => factorial arg✝ -/
#guard_msgs in
  #expand (postfix:200 "!" => factorial)
