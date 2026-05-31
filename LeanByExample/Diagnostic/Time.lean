/- # \#time
`#time` は、コマンドの実行時間を計測するためのコマンドです。ミリ秒単位で結果を出してくれます。
-/

-- フィボナッチ数列の遅い実装
-- `n` に関して指数関数的な時間がかかる
def fibonacci : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fibonacci n + fibonacci (n + 1)

-- 環境にもよるが、1000ms以上かかってしまうことも
#time #eval fibonacci 32

-- フィボナッチ数列のより速い実装
-- `n` に関して線形時間で計算できる
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

/-
```admonish warning title="注意"
エディタ上から [`#eval`](./Eval.md) コマンドで実行したり、コマンドラインで `lean --run` で実行したときにはインタプリタが使用されます。これにより計測できる実行時間は、コンパイル後のバイナリの実行時間とは異なります。

コンパイル後のバイナリの実行時間を計測するには [`lean_exe`](https://github.com/leanprover/lean4/tree/master/src/lake#binary-executables) という `lakefile` のオプションを使用してください。
```
-/

/- ## 舞台裏
`IO.monoMsNow` という関数でそのときの時刻をミリ秒単位で取得できます。これにより `#time` コマンドのような時間計測を行うコマンドを自作できるでしょう。また `IO.monoNanosNow` という関数も存在し、これはナノ秒単位で結果を取得します。これを使うと、単位がナノ秒であるような `#time` の派生コマンドを自作できます。

{{#include ./Time/NanoTime.md}}
-/
