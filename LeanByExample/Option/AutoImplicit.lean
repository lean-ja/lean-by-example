/- # autoImplicit
`autoImplicit` オプションは、自動束縛暗黙引数(auto bound implicit arguments)という機能を制御します。類似オプションとして [`relaxedAutoImplicit`](./RelaxedAutoImplicit.md) があります。

有効にすると、宣言が省略された引数が1文字であるとき、それを暗黙引数として自動的に追加します。
-/
import Lean --#
set_option relaxedAutoImplicit false --#

-- `autoImplicit` が無効の時
set_option autoImplicit false in

-- `nonempty` の定義には `α` という未定義の識別子が含まれるため、エラーになる
/-⋆-//-- error: unknown identifier 'α' -/
#guard_msgs in --#
def nonempty : List α → Bool
  | [] => false
  | _ :: _ => true

-- `autoImplicit` が有効の時
set_option autoImplicit true in

-- `α` という未定義の識別子を含んでいてもエラーにならない。
-- 勝手に暗黙引数として追加されている
def head : List α → Option α
  | [] => none
  | x :: _ => some x

/- 1文字の未束縛の識別子であればなんでも対象になるようです。 -/
section autoImpl

-- `autoImplicit` が有効の時
set_option autoImplicit true

  -- ギリシャ文字ではなくて1文字の小文字でも暗黙引数として追加される
  def nonempty₂ : List a → Bool
    | [] => false
    | _ :: _ => true

  -- `ℱ` も暗黙引数になる
  def nonempty₃ : List ℱ → Bool
    | [] => false
    | _ :: _ => true

  -- ２文字の識別子は暗黙引数として追加されない
  /-⋆-//-- error: unknown identifier 'AB' -/
  #guard_msgs in --#
    def nonempty₄ : List AB → Bool
      | [] => false
      | _ :: _ => true

end autoImpl
