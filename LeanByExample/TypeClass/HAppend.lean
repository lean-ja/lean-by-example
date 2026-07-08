/- # HAppend

`HAppend` (heterogeneous append) は、`++` という二項演算子のための型クラスです。
`++` 記法が何を意味するかについての制約はありません。
任意の型 `α, β, γ : Type` に対して連結 `(· ++ ·) : α → β → γ` を定義することができます。
-/

-- 最初は `++` 記号が定義されていないのでエラーになる
#check_failure ([1, 2] ++ (3 : Nat))

/-- HAppend 型クラスのインスタンスを実装する -/
instance : HAppend (List Nat) Nat (List Nat) where
  hAppend xs n := xs.concat n

-- 連結記号が使えるようになった
#guard [1, 2] ++ (3 : Nat) = [1, 2, 3]

/- 標準ライブラリには、`Array α` に `List α` を連結して `Array α` を得る
`HAppend (Array α) (List α) (Array α)` インスタンスが定義されています。-/

-- Array に List を連結して Array を得ることができる
#guard #[1, 2] ++ [3, 4] = (#[1, 2, 3, 4] : Array Nat)

/- 連結 `(· ++ ·) : α → β → γ` が一つの型の中で閉じているとき、つまり `α = β = γ` のときは [`Append`](#{root}/TypeClass/Append.md) が使用できます。 -/
