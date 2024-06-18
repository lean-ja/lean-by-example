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
/-- info: 3 ≃ 7 mod 4 : Prop -/
#guard_msgs in #check (3 ≃ 7 mod 4)

/- `notation` 記号で定義した記法が実際にどのように展開されているのか確かめるには，`pp.notation` というオプションを無効にします．-/

section

/-- 階乗関数 -/
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

/-- 階乗関数を表す記法 -/
notation a "!" => factorial a

-- 表示する際に導入された記法を無効にする
set_option pp.notation false

/-- info: factorial 5 : Nat -/
#guard_msgs in #check 5!

end

/- ## 優先順位
`notation` で記法を定義するときに，その記法が他の演算子などと比べて結合優先度がどの程度高いかという優先順位(precedence)を数値で指定することができます．優先順位が高い演算子ほど，他の演算子より先に適用されます．
-/

/-- 結合が弱い方. 中身は足し算 -/
notation:0 a " weak " b => Nat.add a b

/-- 結合が強い方．中身は掛け算 -/
notation:70 a " strong " b => Nat.mul a b

-- weak と strong の結合優先度は strong の方が高いので，
-- まず 1 strong 2 が計算されて 2 になり，
-- その後 3 weak 2 が計算されて 5 になる.
#guard (3 weak 1 strong 2) = 5

/-- 優先順位を指定しないで定義した記法. 中身はべき乗 -/
notation a " middle " b => Nat.pow a b

-- デフォルトで middle の優先順位は優先順位 0 のものより低い
#guard (2 middle 1 weak 3) = 16
#guard (2 middle 1 strong 3) = 8


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
