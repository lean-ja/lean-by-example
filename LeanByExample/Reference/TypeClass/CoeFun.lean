/-
# CoeFun
`CoeFun` クラスのインスタンスを与えると、関数ではない項を関数型に強制することができます。
-/

/-- 加法的な関数の全体 -/
structure AdditiveFunction : Type where
  /-- 関数部分 -/
  toFun : Nat → Nat

  /-- 加法を保つ -/
  additive : ∀ x y, toFun (x + y) = toFun x + toFun y

/-- 恒等写像 -/
def identity : AdditiveFunction := ⟨id, by intro _ _; rfl⟩

-- `identity` の型は `AdditiveFunction` であって、関数ではないのでこれはエラーになる
#guard_msgs (drop warning) in --#
#check_failure (identity 1)

-- 関数に変換してからならOK
#check (identity.toFun 1)

section --#
-- `CoeFun` を使って関数への変換を自動化する
local instance : CoeFun AdditiveFunction (fun _ => Nat → Nat) where
  coe f := f.toFun

-- まるで関数のように使えるようになる
#check (identity 1)

end --#
/- 上記の例ではどんな `t : AdditiveFunction` も同じ型 `Nat → Nat` に強制していますが、実際には依存関数型に強制することができます。-/
/- ## Coe との違い
上記の例を、[`Coe`](./Coe.md) を使って再現しようとして下記のようにしても上手くいかないことに注意して下さい。-/
section --#

-- `Coe` で `Nat → Nat` への変換を自動化しようとしている例
local instance : Coe AdditiveFunction (Nat → Nat) where
  coe f := f.toFun

-- `Nat → Nat` への型強制が呼び出されず、エラーになってしまう
-- これは、期待されている型が `Nat → Nat` ではなく、単に `Nat → ?_` であるため。
/--
warning: function expected at
  identity
term has type
  AdditiveFunction
-/
#guard_msgs in
  #check_failure (identity 1)

-- 期待される型を明記すればエラーにならない
#check ((identity : Nat → Nat) 1)

end --#
