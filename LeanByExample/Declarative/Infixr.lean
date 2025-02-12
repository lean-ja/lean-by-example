/- # infixr

`infixr` は、右結合の中置記法を定義するためのコマンドです。
-/
import Lean --#
-- 中置記法の2項演算子を定義。中身はただの引き算
infixr:60 " ⋄ " => fun x y => x - y

-- 右結合になっている
#guard (16 ⋄ 5) ⋄ 4 = 7
#guard 16 ⋄ (5 ⋄ 4) = 15
#guard 16 ⋄ 5 ⋄ 4 = 15

/- ## 舞台裏

`infixr` は [`notation`](#{root}/Declarative/Notation.md) コマンドに展開されるマクロとして実装されています。
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

/-- info: notation:60 lhs✝:61 " ⋄ " rhs✝:60 => (fun x y => x - y) lhs✝ rhs✝ -/
#guard_msgs in
  #expand (infixr:60 " ⋄ " => fun x y => x - y)
