/- # HMul

`HMul` (heterogeneous multiplication)は `*` という二項演算子のための型クラスです。`*` 記号が何を意味するかについての制約はありません。任意の型 `α, β, γ : Type` に対して乗算 `(· * ·) : α → β → γ` を定義することができます。
-/

-- メタ変数の番号を表示しない
set_option pp.mvars false

-- 最初は `*` 記号が定義されていないのでエラーになる
#check_failure [1, 2, 3] * [4, 5, 6]

/-- `HMul` のインスタンスを定義する。
`List Nat` 同士の積を、要素ごとの積で定義した。-/
instance : HMul (List Nat) (List Nat) (List Nat) where
  hMul xs ys := List.zipWith (· * ·) xs ys

-- 乗算記号が使えるようになった
#guard [1, 2, 3] * [4, 5, 6] = [4, 10, 18]
