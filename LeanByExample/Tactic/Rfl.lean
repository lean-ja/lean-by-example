/- # rfl

`rfl` は、**definitionally equal** なもの同士が等しいことを示すタクティクです。-/

/-- 自前で定義した自然数 -/
inductive MyNat where
  | zero
  | succ (n : MyNat)

namespace MyNat
  /- ## 足し算の定義 -/

  /-- MyNat の足し算 -/
  def add : MyNat → MyNat → MyNat
    | a, .zero => a
    | a, .succ b => .succ (add a b)

  /-- MyNat.add を `+` で書けるようにする -/
  instance : Add MyNat where
    add := MyNat.add

end MyNat

/-- 1 に相当する項 -/
def MyNat.one : MyNat := .succ zero

/-- 2 に相当する項 -/
def MyNat.two : MyNat := .succ one

/-- 1 + 1 = 2 に相当する命題 -/
example : MyNat.one + MyNat.one = MyNat.two := by
  rfl

-- definitionally equal でないと証明できない
/-⋆-//--
error: tactic 'rfl' failed, the left-hand side
  MyNat.one
is not definitionally equal to the right-hand side
  MyNat.two
⊢ MyNat.one = MyNat.two
-/
#guard_msgs in --#
example : MyNat.one = MyNat.two := by
  rfl

/- ## \#reduce コマンドとの関係

ここで definitionally equal というのは、おおむね [`#reduce`](#{root}/Diagnostic/Reduce.md) コマンドに与えた結果の式が等しいという意味です。 -/
section
  /- ## rfl で等しいと示せるもの同士の #reduce の出力が等しいことの確認 -/

  -- フィールド記法を無効にする
  set_option pp.fieldNotation false

  /-⋆-//-- info: MyNat.succ (MyNat.succ MyNat.zero) -/
  #guard_msgs in --#
  #reduce MyNat.one + MyNat.one

  /-⋆-//-- info: MyNat.succ (MyNat.succ MyNat.zero) -/
  #guard_msgs in --#
  #reduce MyNat.two
end
/- ただし、`rfl` で示せる等式と、[`#reduce`](#{root}/Diagnostic/Reduce.md) コマンドでの両辺の簡約結果が等しい等式とは完全には一致しません。以下のように、両辺の `#reduce` 結果は異なるものの `rfl` で示せる等式も存在します。 -/
section
  variable {α : Type} {β : α → Type} (f : (x : α) → β x)

  /-⋆-//-- info: f -/
  #guard_msgs in --#
  #reduce f

  /-⋆-//-- info: fun x => f x -/
  #guard_msgs in --#
  #reduce (fun x => f x)

  example : f = (fun x => f x) := by
    rfl

end
/- ## カスタマイズ

`rfl` は、実は等式だけでなく一般の反射的(reflexive)な関係 `R` に対して関係式 `R a b` を示すために使用することができます。ここで二項関係 `R : α → α → Prop` が反射的であるとは、任意の `∀ a, R a a` が成り立つことをいいます。

関係 `R` が反射的であることを `rfl` に利用させるには、`R` の反射性を示した定理に `[refl]` 属性を付与します。-/

-- `MyEq` という二項関係を定義する
inductive MyEq.{u} {α : Type u} : α → α → Prop where
  | refl (a : α) : MyEq a a

example (n : Nat) : MyEq n n := by
  -- `rfl` で示すことはできない。
  fail_if_success rfl

  apply MyEq.refl

-- `MyEq` が反射的であることを登録する
attribute [refl] MyEq.refl

-- `rfl` で示せるようになった！
example (n : Nat) : MyEq n n := by rfl
