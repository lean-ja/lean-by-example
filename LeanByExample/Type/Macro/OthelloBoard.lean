import Lean

/-- 盤面の１セルの状態 -/
inductive Cell where
  /-- 空のセル -/
  | empty
  /-- 黒のセル -/
  | black
  /-- 白のセル -/
  | white
deriving Inhabited, Repr, BEq

/-- 盤面の１セルを表す構文カテゴリ -/
declare_syntax_cat cell

/-- 盤面の何も置かれていない箇所 -/
syntax "-" : cell
/-- 盤面の黒のセル -/
syntax "●" : cell
/-- 盤面の白のセル -/
syntax "○" : cell

open Lean Macro

/-- cellの構文展開 -/
def expandCell (stx : TSyntax `cell) : MacroM (TSyntax `term) := do
  match stx with
  | `(cell| -) => `(Cell.empty)
  | `(cell| ○) => `(Cell.white)
  | `(cell| ●) => `(Cell.black)
  | _ => throwUnsupported

open Parser TSyntax

syntax row := withPosition((lineEq cell)*)
syntax (name := boardStx) "board" withoutPosition(sepByIndentSemicolon(row)) : term

/-- rowの構文展開 -/
def expandRow (stx : TSyntax `row) : MacroM (TSyntax `term) := do
  match stx with
  | `(row| $cells:cell*) => do
    let cells ← cells.mapM expandCell
    `(term| #[ $[$cells],* ])
  | _ => throwUnsupported

macro_rules
  | `(term| board $rows:row*) => do
    let rows ← (rows : TSyntaxArray `row).mapM expandRow
    `(term| #[ $[$rows],* ])

#check board
  - - - -
  - ● ○ -
  - ○ ● -
  - - - -
