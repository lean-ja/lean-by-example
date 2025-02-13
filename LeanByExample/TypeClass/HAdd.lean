/- # HAdd
`HAdd` (heterogeneous addition)は、`+` という二項演算子のための型クラスです。
`+` 記法が何を意味するかについては制約はありません。
任意の型 `α, β, γ : Type` に対して足し算 `(· + ·) : α → β → γ` を定義することができます。
-/

-- 最初は `+` 記号が定義されていないのでエラーになる
#check_failure 1 + (· + 2)

/-- HAdd 型クラスのインスタンスを実装する -/
instance : HAdd Nat (Nat → Nat) (Nat → Nat) where
  hAdd n f := fun m => n + f m

-- 足し算記号が使えるようになった
#check 1 + (· + 2)
