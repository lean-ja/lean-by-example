/- # match .. with

`match .. with` は、**パターンマッチ(pattern match)** に使用されます。

## 基本的な使い方

### コンストラクタによるパターンマッチ

典型的な使用場面は、帰納型 `T` の項は必ずその有限個のコンストラクタの項のどれかに由来するので、そのどれであるかによって場合分けをしたいときです。
-/

def List.myHead? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: _ => some x

#guard [1, 2, 3].myHead? = some 1

/-- 階乗関数。 -/
def Nat.fatorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | m + 1 => (m + 1) * fatorial m

#guard Nat.fatorial 4 = 1 * 2 * 3 * 4

/- パターンマッチの `|` に続くのはコンストラクタの像または、コンストラクタの像に展開される式である必要があります。この挙動を変更して任意の関数を使いたい場合、[`[match_pattern]`](#{root}/Attribute/MatchPattern.md)属性の使用を検討してください。 -/

/- ### 無名コンストラクタによるパターンマッチ
`match .. with` 構文はある程度賢く、[無名コンストラクタ](#{root}/Parser/AnonymousConstructor.md)を展開したりすることができます。 -/

/-- 正の自然数 -/
abbrev Pos := { x : Nat // x > 0 }

/-- 正の自然数に対する階乗関数 -/
def Pos.factorial (n : Pos) : Nat :=
  match n with
  | ⟨1, _⟩ => 1
  | ⟨m + 2, h⟩ => (m + 2) * factorial ⟨m + 1, by omega⟩

#guard Pos.factorial ⟨4, by omega⟩ = 1 * 2 * 3 * 4

/- ## マッチ結果の証明を取得する

`x : T` についてパターンマッチしてコンストラクタ `cons` の枝に入った時、`x` が `cons` に由来するという証明を取得したいことがあります。このとき、`match h : x with` という構文を使用すると、`h` にその証明が格納されます。
-/

def List.myTail {α : Type} (l : List α) : List α :=
  match h : l with
  | [] => []
  | x :: xs => by
    -- `l` が `x :: xs` という形をしていることの証明が取得できている
    guard_hyp h : l = x :: xs
    exact xs

/- ## @ パターン

部分にマッチしつつ、その全体の値を変数として保持したいとき、@ パターンと呼ばれる構文が利用できます。
-/

/-- 自然数を１桁ごとのリストに変換する -/
def Nat.toListNat (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | m@(n + 1) =>
    have : m / 10 < m := by grind
    Nat.toListNat (m / 10) ++ [(m % 10)]

#guard Nat.toListNat 1234 == [1, 2, 3, 4]
