/- # s!

`s!` は、文字列補間を行うための構文です。
-/

def greet (name : String) : String :=
  s!"Hello, {name}!"

/-⋆-//-- info: "Hello, World!" -/
#guard_msgs in --#
#eval greet "World"

/- ## カスタマイズ
`s!` 構文は組み込まれた変数に [`ToString`](#{root}/TypeClass/ToString.md) を適用します。 -/
section
  -- ## test for ambiguous string

  /-⋆-//--
  info: s!: Hello, world ⏎
  s!: Hello, "world"
  -/
  #guard_msgs (whitespace := lax) in --#
  #eval
    let a := "world "
    dbg_trace s!"s!: Hello, {a}"

    let b := "\"world\""
    dbg_trace s!"s!: Hello, {b}"
    return ()
end
/- 代わりに [`Repr`](#{root}/TypeClass/Repr.md) を使うように置き換えることができます。 -/
section
  open Lean TSyntax.Compat

  def Lean.TSyntax.expandInterpolatedStrChunks' (chunks : Array Syntax) (mkAppend : Syntax → Syntax → MacroM Syntax) (mkElem : Syntax → MacroM Syntax) : MacroM Syntax := do
    let mut i := 0
    let mut result := Syntax.missing
    for elem in chunks do
      let elem ←
        match elem.isInterpolatedStrLit? with
        | none => mkElem elem
        | some str => pure <| Syntax.mkStrLit str
      if i == 0 then
        result := elem
      else
        result ← mkAppend result elem
      i := i+1
    return result

  def Lean.TSyntax.expandInterpolatedStr' (interpStr : TSyntax interpolatedStrKind) (type : Term) (toTypeFn : Term) : MacroM Term := do
    let r ← expandInterpolatedStrChunks' interpStr.raw.getArgs (fun a b => `($a ++ $b)) (fun a => `($toTypeFn $a))
    `(($r : $type))
end

syntax:max "d!" interpolatedStr(term) : term

macro_rules
  | `(d! $interpStr) => do interpStr.expandInterpolatedStr' (← `(String)) (← `(reprStr))

section

  /-⋆-//--
  info: d!: Hello, "world "
  d!: Hello, "\"world\""
  -/
  #guard_msgs (whitespace := lax) in --#
  #eval
    let a := "world "
    dbg_trace d!"d!: Hello, {a}"

    let b := "\"world\""
    dbg_trace d!"d!: Hello, {b}"
    return ()
end
