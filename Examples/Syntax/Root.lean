/-
# \_root\_

`_root_` は名前空間のルートを表します．主に名前空間を一時的に抜けるために使います．名前空間 `Hoge` の中で `foo` を定義すると `Hoge.foo` という名前になりますが，`_root_.foo` と定義すればこの挙動を避けて `foo` という名前にすることができます．

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
