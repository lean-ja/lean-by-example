/- # irreducible

`[irreducible]` 属性を付与すると、その名前が定義本体に **定義的に等しい(definitionally equal)** ということが隠されて、[`rfl`](#{root}/Tactic/Rfl.md) タクティクや [`dsimp`](#{root}/Tactic/Dsimp.md) タクティクが通らなくなります。
-/

/-- 階乗関数 -/
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | m + 1 => (m + 1) * factorial m

example : factorial 5 = 120 := by
  -- 最初は rfl が通る
  rfl

example : factorial 5 = 120 := by
  -- dsimp も通る
  dsimp [factorial]

-- [irreducible]属性を与える
attribute [irreducible] factorial

example : factorial 5 = 120 := by
  -- rfl が通らなくなる
  fail_if_success rfl
  -- dsimp も通らない
  fail_if_success dsimp [factorial]

  cbv

-- 補足: 名前を定義に展開しなくてもわかる等式は、引き続き rfl で示せる
example : factorial 5 = factorial 5 := by
  rfl

/- なお [`unfold`](#{root}/Tactic/Unfold.md) タクティクは `[irreducible]` 属性が付与されていても使えます。 -/

example : factorial 5 = 120 := by
  repeat unfold factorial
  rfl

/- また、名前からは [`#reduce`](#{root}/Diagnostic/Reduce.md) コマンドが使えなくなるような印象を受けますが、`#reduce` は相変わらず使用可能です。 -/

-- `#reduce` は相変わらずできる
/-- info: 6 -/
#guard_msgs in --#
#reduce factorial 3

/- ## 用途

ユーザが明確に、自分で定義した関数・定数に対して `[irreducible]` 属性を付与すべき場面はそんなに多くないと筆者は思います。
Lean は[整礎再帰な関数](#{root}/Modifier/TerminationBy.md)や [`partial_fixpoint`](#{root}/Modifier/PartialFixpoint.md) により修飾された関数に対して自動的に `[irreducible]` 属性を付与するのですが、おそらくこの属性を見かけるのはそういう場面が多いでしょう。

[`#print`](#{root}/Diagnostic/Print.md) コマンドを使うと裏で属性が付与されている様子を確認することができます。
-/

def searchF {α : Type} (f : Nat → Option α) (start : Nat) : Option Nat :=
  match f start with
  | some _ => some start
  | none => searchF f (start + 1)
partial_fixpoint

-- `partial_fixpoint` を使ったので irreducible になっている
/--
info: @[irreducible] def searchF : {α : Type} → (Nat → Option α) → Nat → Option Nat :=
fun {α} f =>
  Lean.Order.fix
    (fun f_1 start =>
      match f start with
      | some val => some start
      | none => f_1 (start + 1))
    ⋯
-/
#guard_msgs in --#
#print searchF

/-- 文字列の左側を指定文字で埋めて、指定長にそろえる（整礎再帰バージョン）-/
def String.padLeftWF (input : String) (padChar : Char) (length : Nat) : String :=
  if input.length ≥ length then
    input
  else
    String.padLeftWF (padChar.toString ++ input) padChar length
termination_by length - input.length

-- 整礎再帰を使ったので `[irreducible]` になっている
/--
info: @[irreducible] def String.padLeftWF : String → Char → Nat → String :=
fun input padChar length => String.padLeftWF._unary padChar length input
-/
#guard_msgs in --#
#print String.padLeftWF
