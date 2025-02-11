/- # show_term

`show_term` は、タクティクで作られた項を明示的に表示します。

タクティクは、表面的には「証明を行うためのツール」として振る舞いますが、実際には「示すべき命題に対して、その命題を型に持つような証明項を生成するプログラム」です。裏で生成されている項は普段ユーザからは隠されていますが、`show_term` はそれを見えるようにします。
-/
import Lean

example (n : Nat) : n + 0 = n := by
  rfl

-- `show_term` で `rfl` が生成している具体的な項を表示
/-- info: Try this: Eq.refl (n + 0) -/
#guard_msgs in
  example (n : Nat) : n + 0 = n := show_term by
    rfl

/- ## by? 構文
[`by`](#{root}/Parser/By.md) を `by?` に変えることでも、`show_term` を呼び出すことができます。-/

/-- info: Try this: Eq.refl (n + 0) -/
#guard_msgs in
  example (n : Nat) : n + 0 = n := by?
    rfl

/- 実際、`by?` は `show_term` に展開されるマクロです。-/
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

/-- info: show_term by rfl -/
#guard_msgs in
  #expand (by? rfl)
