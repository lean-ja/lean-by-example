import Lean

open Std

/-- 各文字に対してそれが最後に現れた位置を記録する辞書 -/
abbrev CharPosMap := HashMap Char Nat

/--
文字列`s = c₀c₁...cₙ`と`k : Nat`に対して、
`c₀c₁...cₖ`の末尾部分がなす、最長の重複なし部分列の長さ`currₖ`を計算する。

#### 前提条件
ただし以下は既知であるものとする。
* `lts`: `longestTrailingSubstring.step s (k - 1)`。
  `c₀c₁...cₖ₋₁`の末尾部分がなす、最長の重複なし部分列の長さを表す。
* `last`: `c₀c₁...cₖ₋₁`の中で、各文字が最後に現れた位置を記録する辞書。

#### 返り値
* `lts`: `c₀c₁...cₖ`の末尾部分がなす、最長の重複なし部分列の長さ。
* `last`: `c₀c₁...cₖ`の中で、各文字が最後に現れた位置を記録する辞書。
-/
def longestTrailingSubstring.step (s : String) (k : Nat) (lts : Nat) (last : CharPosMap) : Nat × CharPosMap :=
  let cₖ := s.get! ⟨k⟩
  let prev := last.get? cₖ
  match prev with
  | none =>
    -- `cₖ`は初めて出現するので、重複なしに`cₖ`を追加することができる
    (lts + 1, last.insert cₖ k)
  | some prev =>
    -- 「`c₀c₁...cₖ₋₁`の末尾部分がなす、最長の重複なし部分列」の開始位置
    let start := k - lts
    if prev < start then
      -- `cₖ`はウィンドウの外にあるので、重複を生むことなしに追加できる
      (lts + 1, last.insert cₖ k)
    else
      -- `cₖ`はウィンドウの中にあるので、追加すると重複を生じる。
      -- 重複がなくなるようにウィンドウの左端を落とす。
      let newStart := prev + 1
      (k - newStart + 1, last.insert cₖ k)

/-- 文字列`s = c₀c₁...cₙ`と`k : Nat`に対して、
`c₀c₁...cₖ`の末尾部分がなす、最長の重複なし部分列の長さ`currₖ`を計算して、
配列`#[curr₀, curr₁, ..., currₖ]`を返す。 -/
def longestTrailingSubstring (s : String) : Array Nat := Id.run do
  let mut result : Array Nat := #[]
  let mut lts := 0
  let mut last : CharPosMap := {}
  for k in [0 : s.length] do
    let (lts', last') := longestTrailingSubstring.step s k lts last
    result := result.push lts'
    lts := lts'
    last := last'
  return result

/-- 文字列`s`に対して、最長の重複なし部分列の長さを返す。 -/
def longestSubstring (s : String) : Nat :=
  longestTrailingSubstring s |>.foldl (fun acc x => max acc x) 0

#guard longestSubstring "abcabcbb" = 3
#guard longestSubstring "bbbbb" = 1
#guard longestSubstring "pwwkew" = 3
#guard longestSubstring "abcde" = 5
#guard longestSubstring "a" = 1
#guard longestSubstring "" = 0
