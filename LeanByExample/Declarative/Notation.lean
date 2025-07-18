/- # notation

`notation` は、新しい記法を導入するためのコマンドです。
-/

/-- 各 `k` に対して、二項関係 `a ≃ b mod k` を返す -/
def modulo (k a b : Int) : Prop :=
  k ∣ (a - b)

-- mod という記法を導入する
notation:60 a:60 " ≃ " b:60 " mod " k:60 => modulo k a b

-- 定義した記法が使える
#check (3 ≃ 7 mod 4)

/- `notation` 記号で定義した記法が実際にどのように展開されているのか確かめるには、`pp.notation` というオプションを無効にします。-/

section

  /-- 階乗関数 -/
  def factorial : Nat → Nat
    | 0 => 1
    | n+1 => (n+1) * factorial n

  /-- 階乗関数を表す記法 -/
  notation:100 a:100 "!" => factorial a

  -- 表示する際に導入された記法を無効にする
  set_option pp.notation false

  /-⋆-//-- info: factorial 5 : Nat -/
  #guard_msgs in --#
  #check 5!

end

/- ## パース優先順位
`notation` コマンドで記法を定義するときに、その記法の他の演算子などと比べた **パース優先順位(parsing precedence)** を数値で指定することができます。パース優先順位が高い演算子ほど、他の演算子より先に適用されます。言い換えれば、パース優先順位を正しく設定することにより、括弧を省略しても意図通りに式が解釈されるようにすることができます。
-/

/-- 結合が弱い方。中身は足し算 -/
notation:min a:min " weak " b:min => Nat.add a b

/-- 結合が強い方。中身は掛け算 -/
notation:70 a:70 " strong " b:70 => Nat.mul a b

example : (3 weak 1 strong 2) = 5 := calc
  -- weak と strong のパース優先順位は strong の方が高いので、
  -- まず 1 strong 2 が計算されて 2 になり、
  _ = (3 weak 2) := rfl
  -- その後 3 weak 2 が計算されて 5 になる。
  _ = 5 := rfl

example : (2 strong 2 weak 3) = 7 := calc
  _ = (4 weak 3) := rfl
  _ = 7 := rfl

/- パース優先順位についての構文は [`syntax`](#{root}/Declarative/Syntax.md) コマンドでも同様です。 -/

/- ### プレースホルダのパース優先順位
プレースホルダのパース優先順位の数字は、「この位置に来る記号は、指定された数字以上のパース優先順位を持たなければならない」ことを意味します。下記の例の場合、仮に右結合になるとすると `LXOR` 自身のパース優先順位が `60` でしかなくて `61` 以上という制約を満たさないため、右結合になることがありえないことがわかります。
-/

-- 右側のプレースホルダのパース優先順位を１だけ高くした
notation:60 a:60 " LXOR " b:61 => !a && b

-- 左結合だった場合の値
#guard (true LXOR false) LXOR true = true
-- 右結合だった場合の値
#guard true LXOR (false LXOR true) = false

-- 左結合になることがわかる
#guard true LXOR false LXOR true = true

/- 逆にすると右結合になります。-/

notation:60 a:61 " RXOR " b:60 => a && !b

-- 左結合だった場合の値
#guard (true RXOR false) RXOR true = false
-- 右結合だった場合の値
#guard true RXOR (false RXOR true) = true

-- 右結合になることがわかる
#guard true RXOR false RXOR true = true

/- ### パース優先順位を省略する場合
パース優先順位を省略することもできます。Lean は結合順序に指定がなければ右結合になるようにするようです。-/

/-- パース優先順位を全く指定しないで定義した記法。中身はべき乗 -/
notation a " -^ " b => Nat.pow a b

-- この場合は `weak` (優先順位最低)が先に適用される
example : (2 -^ 1 weak 3) = 16 := calc
  _ = (2 -^ 4) := rfl
  _ = 16 := rfl

-- 一方で次の書き方だと `-^` の方が先に適用される
example : (2 weak 1 -^ 3) = 3 := calc
  _ = (2 weak 1) := rfl
  _ = 3 := rfl

-- ここでも右結合になっている
example : (2 weak 3 -^ 1 weak 2) = 29 := calc
  _ = (2 weak 3 -^ 3) := rfl
  _ = (2 weak 27) := rfl
  _ = 29 := rfl

/- パース優先順位を一部だけ指定することもできます。-/

/-- パース優先順位を部分的に省略した足し算 -/
notation:min a " -+ " b => Nat.add a b

/-- パース優先順位を部分的に省略した掛け算 -/
notation a " -* " b:70 => Nat.mul a b

-- この場合だと、`-*` が先に適用される
-- 仮に `-+` が先に適用されたとすると、
-- `-*` の `b:70` の部分に `(2 -+ 3):min` が来ることになるのでおかしい。
-- だから `-*` が先に適用される。
example : (2 -* 2 -+ 3) = 7 := calc
  _ = (4 -+ 3) := rfl
  _ = 7 := rfl

/- ## 記法の重複問題
`notation` を使って定義した記法のパース優先順位が意図通りに反映されないことがあります。-/
section

  -- 排他的論理和の記号を定義
  local notation:60 x:60 " ⊕ " y:61 => xor x y

  -- 等号（パース優先順位 50）より優先順位が低いという問題でエラーになる
  -- 上では60で定義しているのに、なぜ？
  #check_failure true ⊕ true = false

  -- 括弧を付けるとエラーにならない
  #check (true ⊕ true) = false

end
/- ここでのエラーの原因は、記法が被っていることです。`⊕` という記法は型の直和に対して既に使用されており、直和記法のパース優先順位が等号より低いためにエラーが発生していました。-/

-- 集合の直和の記号と被っていた。
-- 集合の直和記号は等号よりパース優先順位が低いからエラーになっていた
#check Nat ⊕ Fin 2

/- このケースの場合、`priority` で記法の優先度を指定しても解決されません。 -/
section

  -- 排他的論理和の記号を定義
  local notation:60 (priority := high) x:60 " ⊕ " y:61 => xor x y

  -- やっぱりエラーになる
  #check_failure true ⊕ true = false

  -- 括弧を付けるとエラーにならない
  #check (true ⊕ true) = false

end
/- この問題の解決策は、まず第一に括弧を付けることですが、裏技として記法を上書きしてしまうこともできます。-/
section
  -- ⊕ という記号をオーバーライドする
  -- local コマンドを使っているのは、セクション内でだけ有効にするため
  local macro_rules
  | `($x ⊕ $y) => `(xor $x $y)

  -- もう ⊕ が Sum として解釈されることはなく、エラーにならない
  #guard true ⊕ true = false
  #guard true ⊕ false = true
  #guard false ⊕ true = true
  #guard false ⊕ false = false

  -- 上書きされたので、 Sum の意味で ⊕ を使うことはできなくなった
  #check_failure Nat ⊕ Fin 2
end
/- ## 半角スペースの扱い
なお、`notation` を定義する際に半角スペースを入れることがしばしばありますが、これは表示の際に使われるだけで記法の認識には影響しません。-/
section

  -- 足し算を ⋄ で表す
  -- local コマンドを付けているのは、この記法をセクション内でだけ有効にするため
  local notation a "⋄" b => Add.add a b

  -- ⋄ の左右に半角スペースが入っていない！
  -- 違いはそれだけで、記法としては同様の書き方で認識される
  /-⋆-//-- info: 1⋄2 : Nat -/
  #guard_msgs in --#
  #check 1 ⋄ 2

end
