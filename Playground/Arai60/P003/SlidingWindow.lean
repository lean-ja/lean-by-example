import Playground.Arai60.Lib.String
import Lean

open Std Lean

/-- **TODO** Inhabited インスタンスがなぜか標準ライブラリに欠けている -/
instance : Inhabited Range where
  default := ⟨0, 0, 1, by decide⟩

/-- rangeの左端を一つ右へ（大きくなる方向に）進める -/
def Range.shiftLower (r : Range) : Range :=
  ⟨r.start + 1, r.stop, r.step, r.step_pos⟩

/-- rangeの右端を一つ右へ（大きくなる方向に）進める -/
def Range.shiftUpper (r : Range) : Range :=
  ⟨r.start, r.stop + 1, r.step, r.step_pos⟩

/- # スライドウィンドウ

1. 文字列を先頭から順に走査しながら、「今見ている範囲（ウィンドウ）」内に重複文字があるかを調べる。
2. 重複が見つかったら、その重複文字を含まないようにウィンドウの左端を更新。
3. 毎回ウィンドウの長さを計算し、最大値を記録していく。
-/

def reprSW (sw : HashSet Char) : String :=
  sw.fold (fun acc c => acc.push c) ""

def String.point (s : String) (i : Nat) : String :=
  s[[0 : i]] ++ "[" ++ s[[i : i + 1]] ++ "]" ++ s[[i + 1 : s.length]]

def lengthOfLongestSubstring (s : String) : Nat := Id.run do
  let mut sw : HashSet Char := {}
  let mut wl := 0 -- ウィンドウの下限
  let mut maxLength := 0

  -- 文字列の右端に到達するまで、以下を繰り返す
  for wu in [0 : s.length] do
    let char := s.get! ⟨wu⟩
    dbg_trace s!"現在チェックしている個所: {s.point wu}"

    if sw.contains char then
      dbg_trace s!"ウィンドウに {char} はすでに存在します。"

      -- 重複が見つかったので、ウィンドウの左端を更新
      while sw.contains char do
        sw := sw.erase (s.get! ⟨wl⟩)
        wl := wl + 1
        dbg_trace s!"ウィンドウの左端を更新しました。現在のウィンドウは {reprSW sw} です"

    -- 重複がないので、ウィンドウに追加
    sw := sw.insert char
    dbg_trace s!"ウィンドウに {char} を追加しました。現在のウィンドウは {reprSW sw} です"

    -- ウィンドウの最大長を更新する
    if sw.size > maxLength then
      maxLength := sw.size
      dbg_trace s!"ウィンドウの最大長を更新しました: {maxLength}"

  return maxLength


#guard lengthOfLongestSubstring "abcabcbb" = 3
#guard lengthOfLongestSubstring "bbbbb" = 1
#guard lengthOfLongestSubstring "pwwkew" = 3
