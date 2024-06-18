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
notation a "!" => factorial a

-- 表示する際に導入された記法を無効にする
set_option pp.notation false

/-- info: factorial 5 : Nat -/
#guard_msgs in #check 5!

end
