/- # HAppend

`HAppend` (heterogeneous append) は、`++` という二項演算子のための型クラスです。
任意の型 `α, β, γ : Type` に対して連結 `(· ++ ·) : α → β → γ` を定義することができます。
-/

-- 最初は `++` 記号が定義されていないのでエラーになる
#check_failure ([1, 2] ++ (3 : Nat))

/-- HAppend 型クラスのインスタンスを実装する
注意: これは例示のためのインスタンスで、あまり良いインスタンスではない。 -/
instance : HAppend (List Nat) Nat (List Nat) where
  hAppend xs n := xs.map (· + n)

-- 連結記号が使えるようになった
#guard [1, 2] ++ (3 : Nat) = [4, 5]

/- 連結 `(· ++ ·) : α → β → γ` が一つの型の中で閉じているとき、つまり `α = β = γ` のときは [`Append`](#{root}/TypeClass/Append.md) が使用できます。 -/
