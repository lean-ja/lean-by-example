/-
# 問題 49
(中級 🌟🌟) グレイコード。

nビットのグレイコードは、特定の規則に従って構成されるnビット列の列である。例えば、

```
n = 1: C(1) = ['0','1'].
n = 2: C(2) = ['00','01','11','10'].
n = 3: C(3) = ['000','001','011','010','110','111','101','100'].
```

この構成規則を見つけ、次の仕様の述語を実装せよ:

```
% gray(N,C) :- C is the N-bit Gray code
```

「結果のキャッシュ」手法を使って、繰り返し使う場合により効率的にできるか？
-/

/-- 1ビットを表す型 -/
inductive Digit : Type where
  | zero
  | one
deriving DecidableEq

/-- グレイコードはDigitのリスト -/
abbrev GrayCode := List Digit

/-- Digitを文字列に変換 -/
def Digit.toString : Digit → String
  | .zero => "0"
  | .one => "1"

instance : OfNat Digit 0 where
  ofNat := Digit.zero

instance : OfNat Digit 1 where
  ofNat := Digit.one

instance : ToString Digit where
  toString := Digit.toString

def gray (n : Nat) : List GrayCode :=
  match n with
  | 0 => []
  | 1 => [[.zero], [.one]]
  | n + 1 =>
    let prev := gray n
    let revPrev := prev.reverse
    (prev.map (fun d => Digit.zero :: d)) ++ (revPrev.map (fun d => Digit.one :: d))

#guard gray 1 = [[0], [1]]

#guard gray 2 = [[0, 0], [0, 1], [1, 1], [1, 0]]

#guard gray 3 = [
  [0, 0, 0],
  [0, 0, 1],
  [0, 1, 1],
  [0, 1, 0],
  [1, 1, 0],
  [1, 1, 1],
  [1, 0, 1],
  [1, 0, 0]
]
