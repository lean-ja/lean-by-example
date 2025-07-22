/-
# 問題 28B
(中級 🌟🌟) リストのリストを「長さの頻度」でソートせよ。すなわち、長さが珍しいリストほど先に、頻度が高い長さのリストほど後に並べる。
-/
variable {α : Type}

-- これを使ってよい
#check List.mergeSort

/-- リスト `l` の中で `target` と同じ長さのリストの個数を数える -/
def makeToLengthFreq (l : List (List α)) (target : List α) : Nat :=
  let lengthList := l.map (·.length)
  lengthList.filter (· = target.length) |>.length

def lfsort (l : List (List α)) : List (List α) :=
  List.mergeSort l (fun t s => makeToLengthFreq l t ≤ makeToLengthFreq l s)

#guard lfsort ([[]] : List (List String)) == [[]]
#guard lfsort [[1, 2], [1], [1, 2]] == [[1], [1, 2], [1, 2]]
#guard lfsort [[1, 2], [1], [2, 3]] == [[1], [1, 2], [2, 3]]
