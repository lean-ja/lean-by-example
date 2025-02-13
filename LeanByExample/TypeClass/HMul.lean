/- # HMul

`HMul` (heterogeneous multiplication)は `*` という二項演算子のための型クラスです。`*` 記号が何を意味するかについての制約はありません。任意の型 `α, β, γ : Type` に対して乗算 `(· * ·) : α → β → γ` を定義することができます。
-/

-- 最初は `*` 記号が定義されていないのでエラーになる
#check_failure 2 * (· + 1)

/-- `HMul` のインスタンスを定義する -/
instance : HMul Nat (Nat → Nat) (Nat → Nat) where
  hMul xs ys := fun m => xs * ys m

-- 乗算記号が使えるようになった
#check 2 * (· + 1)
