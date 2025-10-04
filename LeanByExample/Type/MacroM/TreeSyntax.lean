variable {α : Type}

/-- ラベル付き木 -/
inductive Tree (α : Type) where
  | empty
  | node (v : α) (children : List (Tree α))
deriving BEq

/-- 葉(子を持たないノード) -/
def Tree.leaf (v : α) : Tree α := Tree.node v []

open Lean Macro

/-- ラベル付き木のための構文 -/
declare_syntax_cat tree

/-- `φ`が`tree`構文であるならば、`[tree| φ]`はラベル付き木を表す -/
syntax "[tree| " tree "]" : term

/-- 木のラベル。ラベルとしては、数値リテラル・文字列リテラル・文字リテラルを許可する -/
syntax tree_label := num <|> str <|> char

/-- 基底ケース: `[tree| 42]`などは正しい構文 -/
syntax tree_label : tree

/-- 再帰ステップ -/
syntax tree_label " * " "(" sepBy(tree, " + ") ")" : tree

-- 構文のテスト
#check_failure [tree| 42]
#check_failure [tree| 42 * (13 + 22 + 14)]

/-- `tree_label`に属する構文を`term`に変換する -/
def expandTreeLabel (stx : TSyntax `tree_label) : MacroM (TSyntax `term) :=
  match stx with
  | `(tree_label| $num:num) => `(term| $num)
  | `(tree_label| $str:str) => `(term| $str)
  | `(tree_label| $char:char) => `(term| $char)
  | _ => throwUnsupported

/-- 再帰的に`tree`構文を`term`に変換する -/
partial def expandTree (stx : TSyntax `tree) : MacroM (TSyntax `term) := do
  match stx with
  | `(tree| $label:tree_label) =>
    let v ← expandTreeLabel label
    `(term| Tree.leaf $v)
  | `(tree| $label:tree_label * ( $children+* )) =>
    let v ← expandTreeLabel label
    let children ← children.getElems.mapM expandTree
    `(term| Tree.node $v [ $children,* ])
  | _ => throwUnsupported

macro_rules
  | `([tree| $tree_stx:tree]) => expandTree tree_stx

-- マクロ展開のテスト
#guard
  let actual := [tree| 42]
  let expected := Tree.leaf 42
  actual == expected

#guard
  let actual := [tree| "foo" * ("a" + "b" + "c")]
  let expected := Tree.node "foo" [Tree.leaf "a", Tree.leaf "b", Tree.leaf "c"]
  actual == expected
