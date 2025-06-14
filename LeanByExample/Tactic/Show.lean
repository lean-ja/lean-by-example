/- # show

`show` はこれから示すことを宣言するタクティクです。

`show` は、ゴールが特定の命題に等しいかどうかチェックします。`show P` と書くと、ゴールの中に `⊢ P` が存在しないときにエラーになり、存在すればそれをメインのゴールにします。たとえば、証明中にこれから示すべきことを明示し、コードを読みやすくする目的で使うことができます。
-/
import Lean --#
variable (P Q : Prop)

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · show P
    exact hP
  · show Q
    exact hQ

/- ゴールを定義上等しい命題に変形するために使用することもできます。-/

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

example : factorial 3 = 6 := by
  -- 定義上等しいのでゴールを変形できる
  show 3 * factorial 2 = 6

  -- 定義上等しいのでゴールを変形できる
  show 3 * (2 * factorial 1) = 6

  rfl

/- `show` タクティクとよく似た構文を持つものに、[`show .. from`](#{root}/Parser/Show.md) 構文があります。 -/

/- ## 舞台裏
`show` タクティクは、[`show .. from`](#{root}/Parser/Show.md) 構文に展開されるマクロとして定義されています。
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

/-⋆-//-- info: refine_lift show P from ?_ -/
#guard_msgs in --#
#expand (show P)
