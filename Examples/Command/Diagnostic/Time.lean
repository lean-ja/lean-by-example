/- # \#time
`#time` は、コマンドの実行時間を計測するためのコマンドです。ミリ秒単位で結果を出してくれます。
-/
import Mathlib.Util.Time
namespace Time --#

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
エディタ上から [`#eval`](./Eval.md) コマンドで実行したり、コマンドラインで `lean --run` で実行したときにはインタプリタが使用されます。これはコンパイル後のバイナリの実行時間とは異なります。

コンパイル後のバイナリの実行時間を計測するには [`lean_exe`](https://github.com/leanprover/lean4/tree/master/src/lake#binary-executables) という `lakefile` のオプションを使用してください。
```
-/

/- ## 舞台裏
`IO.monoMsNow` という関数でそのときの時刻を取得し、その差を計算することで実行時間を計測することができます。これにより `#time` コマンドと同様のコマンドを自作することができます。
-/

open Lean Elab Command Term Meta

elab "#my_time " stx:command : command => do
  -- 実行直前に計測開始
  let start_time ← IO.monoMsNow

  -- コマンドを実行
  elabCommand stx

  -- 実行後に計測終了
  let end_time ← IO.monoMsNow

  -- 差分を実行時間としてミリ秒単位で出力
  logInfo m!"time: {end_time - start_time}ms"

#my_time #eval fib 32

/- また、派生コマンドを作ることもできます。次に挙げるのは「コマンドが１秒以内に終了するか」を検証するコマンドを自作する例です。-/

elab "#in_second " stx:command : command => do
  let start_time ← IO.monoMsNow
  elabCommand stx
  let end_time ← IO.monoMsNow
  let time := end_time - start_time

  -- 1秒以内に終わったかどうか判定
  -- 終わっていなければエラーにする
  if time <= 1000 then
    logInfo m!"time: {time}ms"
  else
    throwError m!"It took more than one second for the command to run."

-- 1秒以内に終わる
#in_second #eval fib 32

/-- error: It took more than one second for the command to run. -/
#guard_msgs (error) in #in_second #eval fibonacci 32

end Time --#
