/- # HashMap

`Std.HashMap` は、キー（鍵）と値のペアを格納するデータ構造です。-/
import Lean

open Std

#eval ({(1, "hello"), (2, "world")} : HashMap Nat String)

/- `HashMap` を使うと、たとえば「文字列中に登場する文字の出現回数を数える」といった処理が効率的にできます。 -/

/--
文字列中の各文字の出現回数を数えて `HashMap` にまとめる関数。
-/
def countingChars (s : String) : HashMap Char Nat := Id.run do
  -- 空のハッシュマップを作成（キー：文字、値：出現回数）
  let mut counts : HashMap Char Nat := {}
  -- 文字列をリストに変換して1文字ずつ処理
  for c in s.toList do
    -- 既存のカウント値を取得し（なければ 0）、1 を加算して更新
    counts := counts.insert c (counts.getD c 0 + 1)
  -- 完成したハッシュマップを返す
  return counts

#guard (countingChars "").toList == []  -- 空文字列のカウントは空のハッシュマップ
#guard (countingChars "hello")['h']! == 1
#guard (countingChars "hello")['l']! == 2
