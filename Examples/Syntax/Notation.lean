/-
# notation
`notation` は，新しい記法を導入するためのコマンドです．
-/

/-- 各 `k` に対して，二項関係 `a ≃ b mod k` を返す -/
def modulo (k a b : Int) : Prop :=
  k ∣ (a - b)

-- mod という記法を導入する
notation a " ≃ " b " mod " k => modulo k a b

-- 定義した記法が使える
#check (3 ≃ 7 mod 4)

/- `notation` 記号で定義した記法が実際にどのように展開されているのか確かめるには，`pp.notation` というオプションを無効にします．-/

section

/-- 階乗関数 -/
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

/-- 階乗関数を表す記法 -/
notation:100 a:100 "!" => factorial a

-- 表示する際に導入された記法を無効にする
set_option pp.notation false

/-- info: factorial 5 : Nat -/
#guard_msgs in #check 5!

end

/- ## 優先順位
`notation` で記法を定義するときに，その記法が他の演算子などと比べて結合優先度がどの程度高いかという優先順位(precedence)を数値で指定することができます．優先順位が高い演算子ほど，他の演算子より先に適用されます．言い換えれば，優先順位を正しく設定することにより，括弧を省略しても意図通りに式が解釈されるようにすることができます．
-/

/-- 結合が弱い方. 中身は足し算 -/
notation:0 a:0 " weak " b:0 => Nat.add a b

/-- 結合が強い方．中身は掛け算 -/
notation:70 a:70 " strong " b:70 => Nat.mul a b

example : (3 weak 1 strong 2) = 5 := calc
  -- weak と strong の結合優先度は strong の方が高いので，
  -- まず 1 strong 2 が計算されて 2 になり，
  _ = (3 weak 2) := rfl
  -- その後 3 weak 2 が計算されて 5 になる.
  _ = 5 := rfl

example : (2 strong 2 weak 3) = 7 := calc
  _ = (4 weak 3) := rfl
  _ = 7 := rfl

/- 優先順位を省略することもできるのですが，とても意外な挙動になるので推奨できません．必ず優先順位を指定してください．-/

/-- 優先順位を全く指定しないで定義した記法. 中身はべき乗 -/
notation a " bad_pow " b => Nat.pow a b

-- bad_pow の優先順位は優先順位 0 の weak よりも低い？
example : (2 bad_pow 1 weak 3) = 16 := calc
  _ = (2 bad_pow 4) := rfl
  _ = 16 := rfl

-- 一方で次の書き方だと bad_pow の方が先に適用される
-- どうやら右結合が採用されるようだ
example : (2 weak 1 bad_pow 3) = 3 := calc
  _ = (2 weak 1) := rfl
  _ = 3 := rfl

-- 右結合になっている例
example : (2 weak 3 bad_pow 1 weak 2) = 29 := calc
  _ = (2 weak 3 bad_pow 3) := rfl
  _ = (2 weak 27) := rfl
  _ = 29 := rfl


/-- プレースホルダの優先順位を省略した weak -/
notation:20 a " bad_weak" b => Nat.add a b

/-- プレースホルダの優先順位を省略した strong -/
notation:70 a " bad_strong " b => Nat.mul a b

-- bad_strong の方が優先順位が高いと思いきや，
-- 右結合になるので bad_weak の方が先に適用されてしまう
example : (2 bad_strong 2 bad_weak 3) = 10 := calc
  _ = (2 bad_strong 5) := rfl
  _ = 10 := rfl

/- ## 記法の重複問題
`notation` を使って定義した記法の優先順位が意図通りに反映されないことがあります．-/
section --#

-- 排他的論理和の記号を定義
local notation:60 x:60 " ⊕ " y:61 => xor x y

-- 等号（優先順位 50）より優先順位が低いという問題でエラーになる
-- 上では60で定義しているのに，なぜ？
/--
warning: application type mismatch
  Sum true
argument
  true
has type
  Bool : Type
but is expected to have type
  Type ?u.13677 : Type (?u.13677 + 1)
---
info: sorryAx (Type u_1) true ⊕ sorryAx (Type u_2) true : Type (max u_1 u_2)
-/
#guard_msgs in
#check_failure true ⊕ true = false

-- 括弧を付けるとエラーにならない
#check (true ⊕ true) = false

end --#

/- ここでのエラーの原因は，記法が被っていることです．`⊕` という記法は型の直和に対して既に使用されており，直和記法の優先順位が等号より低いためにエラーが発生していました．-/

-- 集合の直和の記号と被っていた．
-- 集合の直和記号は等号より優先度が低いからエラーになっていた
#check Nat ⊕ Fin 2

/- この問題の解決策は，まず第一に括弧を付けることですが，裏技として記法を上書きしてしまうこともできます．-/
section --#
-- ⊕ という記号をオーバーライドする
-- local コマンドを使っているのは，セクション内でだけ有効にするため
local macro_rules | `($x ⊕ $y) => `(xor $x $y)

-- もう ⊕ が Sum として解釈されることはなく，エラーにならない
#guard true ⊕ true = false
#guard true ⊕ false = true
#guard false ⊕ true = true
#guard false ⊕ false = false

-- 上書きされたので， Sum の意味で ⊕ を使うことはできなくなった
#check_failure Nat ⊕ Fin 2
end --#

/- ## 補足
なお，`notation` を定義する際に半角スペースを入れることがしばしばありますが，これは表示の際に使われるだけで記法の認識には影響しません．-/
section

-- 足し算を ⋄ で表す
-- local コマンドを付けているのは，この記法をセクション内でだけ有効にするため
local notation a "⋄" b => Add.add a b

-- ⋄ の左右に半角スペースが入っていない！
-- 違いはそれだけで，記法としては同様の書き方で認識される
/-- info: 1⋄2 : Nat -/
#guard_msgs in #check 1 ⋄ 2

end
