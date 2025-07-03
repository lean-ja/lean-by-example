/- # pp.macroStack オプションについて -/

/- 以下のようにマクロを定義したとする。-/

/-- 自前で定義したリスト型 -/
inductive MyList (α : Type) where
  | nil
  | cons (head : α) (tail : MyList α)
deriving DecidableEq

/-- 空リスト。標準の`List`のための記法と被るのを避けている。 -/
notation:max " ⟦⟧ " => MyList.nil

/-- `MyList`に要素を追加する。標準の`List`のための記法と被るのを避けている。 -/
infixr:80 " ::: " => MyList.cons

/-- 自作のリストリテラル構文。なお末尾のカンマは許可される。
なお標準の`List`のための記法と被るのを避けている。 -/
syntax "⟦" term,*,? "⟧" : term

macro_rules
  | `(⟦$x⟧) => `($x ::: ⟦⟧)
  | `(⟦$x, $xs,*⟧) => `($x ::: (⟦$xs,*⟧))

/- 一見正しそうに見えるが、こんなエラーになってしまう。 -/

#check_failure ⟦1, ⟧

/- こういうときに、マクロがどういう順に展開されて行ってどこでエラーになったかを確認するのに`pp.macroStack`オプションは役に立つ。 -/

set_option pp.macroStack true

/-⋆-//--
info: elaboration function for '«term⟦_⟧»' has not been implemented
  ⟦ ⟧
with resulting expansion
  ⟦ ⟧
while expanding
  (⟦ ⟧)
while expanding
  1 ::: (⟦ ⟧)
while expanding
  ⟦1, ⟧
-/
#guard_msgs in --#
#check_failure ⟦1, ⟧
