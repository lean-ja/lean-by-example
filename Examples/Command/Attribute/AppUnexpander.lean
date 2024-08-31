/- # app_unexpander
`app_unexpander` 属性を付与すると、関数適用 `f a₁ a₂ ... aₙ` の `#check` コマンドや infoview での表示のされ方を変更することができます。
-/

/-- α を全体集合として、その部分集合の全体。
α の部分集合と α 上の述語を同一視していることに注意。 -/
def Set (α : Type) := α → Prop

variable {α : Type}

/-- 述語 `p : α → Prop` に対応する集合 -/
def setOf {α : Type} (p : α → Prop) : Set α := p

/-- 内包表記 `{ x : α | p x }` の `x : α` の部分のための構文。
`: α` の部分はあってもなくてもよいので `( )?` で囲っている。-/
syntax extBinder := ident (" : " term)?

/-- 内包表記 `{ x : α | p x }` の `{ | }` の部分のための構文。 -/
syntax (name := setBuilder) "{" extBinder " | " term "}" : term

/-- 内包表記の意味をマクロとして定義する -/
macro_rules
  | `({ $x:ident : $type | $p }) => `(setOf (fun ($x : $type) => $p))
  | `({ $x:ident | $p }) => `(setOf (fun ($x : _) => $p))

-- 内包表記が使えるようになったが、コマンドの出力や infoview では
-- いま定義した記法が使われないという問題がある
/-- info: setOf fun n => ∃ m, n = 2 * m : Set Nat -/
#guard_msgs in
  #check {n : Nat | ∃ m, n = 2 * m}

/-- infoview やコマンドの出力でも内包表記を使用するようにする -/
@[app_unexpander setOf]
def setOf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $p) => `({ $x:ident | $p })
  | `($_ fun ($x:ident : $ty:term) => $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()

-- 正常に動作することを確認

/-- info: {n | ∃ m, n = 2 * m} : Set Nat -/
#guard_msgs in
  #check {n | ∃ m, n = 2 * m}

/-- info: {n | ∃ m, n = 2 * m} : Set Nat -/
#guard_msgs in
  #check {n : Nat | ∃ m, n = 2 * m}
