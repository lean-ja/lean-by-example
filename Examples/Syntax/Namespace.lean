/-
# namespace
`namespace` は，定義に階層構造を与えて整理するための構文です．名前空間 `Foo` の中で `bar` を定義すると，それは `Foo.bar` という名前になり，名前空間 `Foo` の中では短い名前 `bar` でアクセスできますが，名前空間を出るとアクセスにフルネームが必要になります．

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
