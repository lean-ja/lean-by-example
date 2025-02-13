/- # app_unexpander
`[app_unexpander]` 属性を付与すると、関数適用 `f a₁ a₂ ... aₙ` の `#check` コマンドでの表示のされ方を変更することができます。
-/

/-- 人に挨拶をする関数 -/
def greet (x : String) := s!"Hello, {x}!"

set_option linter.unusedVariables false in --#

/-- すべての挨拶の表示を強制的に hello world に変えてしまう -/
@[app_unexpander greet]
def unexpGreet : Lean.PrettyPrinter.Unexpander
  | `(greet $x) => `("hello world")
  | _ => throw ()

-- #check の表示が上書きされて変わる
/-⋆-//-- info: "hello world" : String -/
#guard_msgs in --#
#check greet "Alice"

-- #eval の表示は変わらない
/-⋆-//-- info: "Hello, Alice!" -/
#guard_msgs in --#
#eval greet "Alice"

/- より実用的な例として、[`macro_rules`](#{root}/Declarative/MacroRules.md) コマンドで定義した集合の内包記法の表示のされ方を制御する例が挙げられます。 -/

/-- α を全体集合として、その部分集合の全体。
α の部分集合と α 上の述語を同一視していることに注意。 -/
def Set (α : Type) := α → Prop

/-- 述語 `p : α → Prop` に対応する集合 -/
def setOf {α : Type} (p : α → Prop) : Set α := p

section
  /- ## 集合の内包表記 -/

  /-- 内包表記 `{ x : α | p x }` の `x : α` の部分のための構文。
  `: α` の部分はあってもなくてもよいので `( )?` で囲っている。-/
  syntax extBinder := ident (" : " term)?

  /-- 内包表記 `{ x : α | p x }` の `{ | }` の部分のための構文。 -/
  syntax (name := setBuilder) "{" extBinder " | " term "}" : term

  /-- 内包表記の意味をマクロとして定義する -/
  macro_rules
    | `({ $x:ident : $type | $p }) => `(setOf (fun ($x : $type) => $p))
    | `({ $x:ident | $p }) => `(setOf (fun ($x : _) => $p))
end

-- 内包表記が使えるようになったが、#check コマンドの出力では
-- いま定義した記法が使われないという問題がある
/-⋆-//-- info: setOf fun n => ∃ m, n = 2 * m : Set Nat -/
#guard_msgs in --#
#check {n : Nat | ∃ m, n = 2 * m}

/-- #check コマンドの出力でも内包表記を使用するようにする -/
@[app_unexpander setOf]
def setOf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $p) => `({ $x:ident | $p })
  | `($_ fun ($x:ident : $ty:term) => $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()

section
  /- ## app_unexpander のテスト -/

  /-⋆-//-- info: {n | ∃ m, n = 2 * m} : Set Nat -/
  #guard_msgs in --#
  #check {n | ∃ m, n = 2 * m}

  /-⋆-//-- info: {n | ∃ m, n = 2 * m} : Set Nat -/
  #guard_msgs in --#
  #check {n : Nat | ∃ m, n = 2 * m}

end
