/- # StateM

`StateM` は、状態を変更するような計算を表現する[モナド](#{root}/TypeClass/Monad.md)です。
`StateM σ α` で、「型 `σ` を持つ状態のデータを読み書きしながら `α` 型の項を返す計算」を表します。

たとえば、フィボナッチ数列の `n` 番目の値を計算しながら、計算過程で生成された中間結果を記録していくような関数は次のように書けます。
-/
import Lean

open Std

/-- フィボナッチ数列の計算過程ログ -/
structure FibLog where
  /-- `n`番目のフィボナッチ数列の値を記録する辞書。
  デフォルト値として`0`番目と`1`番目の値を持たせてある。
  -/
  dict : HashMap Nat Nat := HashMap.ofList [(0, 0), (1, 1)]
deriving Repr

/-- 今までの計算結果を記録しながら、フィボナッチ数列の`n`番目の値を計算する -/
def StateM.fibonacci (n : Nat) : StateM FibLog Nat := do
  match n with
  | 0 => return 0
  | 1 => return 1
  | n + 2 => do
    -- 今までの計算結果を取得しようと試みる
    let dict := (← get).dict

    match dict[n + 2]? with
    | some y =>
      -- すでに計算済みならばそれを返す
      return y
    | none =>
      -- まだ計算していなければ再帰的に計算する
      let x1 ← fibonacci (n + 1)
      let x2 ← fibonacci n
      let y := x1 + x2

      -- 計算結果をログに記録する
      modify fun log => { log with dict := log.dict.insert (n + 2) y }

      return y

/-- `n`番目のフィボナッチ数列を計算する -/
def StateM.nthFib (n : Nat) : Nat :=
  -- 空の状態（つまりデフォルト値で埋められた状態）から出発して、
  -- 計算を実行して値を取り出す
  (StateM.fibonacci n).run' {}

/-- `0`から`n`番目までのフィボナッチ数列を計算する -/
def StateM.seqFib (n : Nat) : List Nat :=
  -- 空の状態から出発して、計算を実行した後、
  -- その時点で状態として保持している値を取り出す
  let (_val, log) := (StateM.fibonacci n).run {}
  Prod.snd <$> log.dict.toList

#guard StateM.nthFib 22 = 17711
#guard StateM.seqFib 10 = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
