/- 文字列 `s` が与えられたとき、その中で最初に**一度しか現れない文字**を見つけて、その\*\*インデックス（位置）\*\*を返してください。
もしそのような文字が存在しない場合は `-1` を返してください。
-/
import Lean

open Std

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

/--
最初に一度だけ現れる文字のインデックスを返す関数。
そのような文字がなければ `none` を返す。
-/
def firstUniqueChar (s : String) : Option Nat := Id.run do
  -- 各文字の出現回数を取得
  let counts := countingChars s
  -- 各文字とそのインデックスの組を順に処理
  for (c, idx) in s.toList.zipIdx do
    -- その文字の出現回数が 1 なら、そのインデックスを返す
    if counts[c]! == 1 then
      return some idx
  -- 一度しか現れない文字がなければ none を返す
  return none

#guard firstUniqueChar "leetcode" == some 0  -- 'l' が最初に一度だけ現れる
#guard firstUniqueChar "loveleetcode" == some 2  -- 'v' が最初に一度だけ現れる
#guard firstUniqueChar "aabb" == none    -- 一度だけ現れる文字が存在しない
#guard firstUniqueChar "" == none    -- 空文字列も none
#guard firstUniqueChar "abcabcde" == some 6  -- 'd' が最初に一度だけ現れる
