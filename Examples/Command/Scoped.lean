/- # scoped
`scoped` は，コマンドの有効範囲を現在の名前空間に限定します．
-/
namespace Scoped
  -- scoped を付けて greet コマンドをマクロとして定義
  scoped macro "greet" : command => `(#eval "hello, world!")

  -- その名前空間の中では greet コマンドが利用できる
  greet

end Scoped

-- 名前空間を抜けると利用できない
#check_failure greet

-- 再び同じ名前で名前空間を開く
namespace Scoped
    -- その名前空間の中では greet コマンドが利用できる
    greet

end Scoped

section
  open Scoped

  -- 単に open するだけでも利用できるようになる
  greet
end

/- `scoped` で有効範囲を限定できるコマンドには，次のようなものがあります．（以下で全部ではありません）
* `elab`, `elab_rules`
* `infix`, `infixl`, `infixr`
* [`notation`](./Notation.md)
* `postfix`
* `prefix`,
* `instance`
* `macro`, `macro_rules`
* `simproc`
* `syntax`
-/
