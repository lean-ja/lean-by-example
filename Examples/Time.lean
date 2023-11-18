import Mathlib.Util.Time -- `#time` を使うため

-- フィボナッチ数列の指数時間の実装
def fibonacci : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fibonacci n + fibonacci (n + 1)

-- 環境にもよるが, 1000ms以上かかってしまうことも
#time #eval fibonacci 32

-- フィボナッチ数列の線形時間の実装
def fib (n : Nat) : Nat :=
  (loop n).1
where
  loop : Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 =>
      let p := loop n
      (p.2, p.1 + p.2)

-- 10 ms 程度で終わる
#time #eval fib 32
