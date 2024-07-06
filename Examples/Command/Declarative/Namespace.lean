/- # namespace
`namespace` は，定義に階層構造を与えて整理するためのコマンドです．名前空間 `Foo` の中で `bar` を定義すると，それは `Foo.bar` という名前になり，名前空間 `Foo` の中では短い名前 `bar` でアクセスできますが，名前空間を出るとアクセスにフルネームが必要になります．

なおここでは説明のために `namespace` の中をインデントしていますが，これは一般的なコード規約ではありません．
-/

-- namespace の外で定義された関数
def greet (name : String) := "Hello, " ++ name

namespace Nat

  def isEven (n : Nat) : Bool := n % 2 == 0

  -- 同じ名前空間の中なら短い名前でアクセスできる
  #check isEven

  -- 名前空間の外にある名前にアクセスできる
  #check greet

end Nat

-- 名前空間の外に出ると，短い名前ではアクセスできない
#check_failure isEven

-- フルネームならアクセスできる
#check Nat.isEven

/- 名前空間は入れ子にすることができます．-/

namespace Nat

  namespace Even

    def thirty := 30

  end Even

  #check Even.thirty

end Nat

#check Nat.Even.thirty

/-
## 名前空間を一時的に抜ける

名前空間を一時的に抜けたいとき，`_root_` が使用できます．名前空間 `Hoge` の中で `foo` を定義すると `Hoge.foo` という名前になりますが，`_root_.foo` と定義すればこの挙動を避けて `foo` という名前にすることができます．

たとえば以下のように名前空間の中で `List` 配下の関数を定義し，フィールド記法を使おうとしてもうまくいきません．こういう場合に `_root_` を使用すると，名前空間を閉じることなくエラーを解消できます．
-/
namespace Root -- 名前空間 `Root` の宣言

variable {α : Type}

def List.unpack (l : List (List α)) : List α :=
  match l with
  | [] => []
  | x :: xs => x ++ unpack xs

/--
error: invalid field 'unpack', the environment does not contain 'List.unpack'
  [[1, 2], [3]]
has type
  List (List Nat)
-/
#guard_msgs (whitespace := lax) in
#check ([[1, 2], [3]] : List (List Nat)).unpack

-- エラーになる原因は，名前空間 `Root` の中で宣言したので
-- 関数名が `Root.List.unpack` になってしまっているから
#check Root.List.unpack

-- `_root_` を頭につけて再度定義する
def _root_.List.unpack (l : List (List α)) : List α :=
  match l with
  | [] => []
  | x :: xs => x ++ unpack xs

-- 今度は成功する
#eval [[1, 2], [3]].unpack

end Root
