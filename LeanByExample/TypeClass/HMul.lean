/- # HMul

`HMul` (heterogeneous multiplication)は `*` という二項演算子のための型クラスです。`*` 記号が何を意味するかについての制約はありません。任意の型 `α, β, γ : Type` に対して掛け算 `(· * ·) : α → β → γ` を定義することができます。
-/

-- 最初は `*` 記号が定義されていないのでエラーになる
#check_failure 2 * (· + 1)

/-- `HMul` のインスタンスを定義する -/
instance : HMul Nat (Nat → Nat) (Nat → Nat) where
  hMul xs ys := fun m => xs * ys m

-- 乗算記号が使えるようになった
#check 2 * (· + 1)


/- 掛け算 `(· * ·) : α → β → γ` が一つの型の中で閉じているとき、つまり `α = β = γ` のときは [`Mul`](#{root}/TypeClass/Mul.md) が使用できます。 -/
