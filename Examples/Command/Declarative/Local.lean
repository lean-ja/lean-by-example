/- # local
`local` はコマンドをその [`section`](./Section.md) の内部でだけ有効にするための修飾子です．
-/

section foo
  -- local を付けて新しい記法を定義
  local notation " succ' " => Nat.succ

  -- section の中では使用できる
  #check succ'
end foo

-- section を抜けると使えなくなる
#check_failure succ'

section foo
  -- 同じ名前の section を再度開いても使えない
  #check_failure succ'
end foo

/- コマンドのスコープを [`namespace`](./Namespace.md) の内部に限定するのにも使えます．ただし，下記のコードで示しているように，`local` で修飾したコマンドの効果は同じ名前空間の中で永続するのではなく, `end` でその名前空間が閉じられたときに消失します．-/

namespace hoge
  -- local を付けて新しい記法を定義
  local notation " succ' " => Nat.succ

  -- 定義した namespace の中では使用できる
  #check succ' 2
end hoge

-- namespace の外では使用できない
#check_failure succ' 2

-- 再び同じ名前の namespace をオープンする
namespace hoge
  -- 使用できない！
  #check_failure succ'
end hoge


/- `local` で有効範囲を限定できるコマンドには，次のようなものがあります．(以下で全部ではありません)
* `elab`, `elab_rules`
* `macro`, `macro_rules`
* `infix`, `infil`, `infixr`
* `postfix`, `postfixl`, `postfixr`
* `prefix`
* [`notation`](./Notation.md)
* [`instance`](./Instance.md)
* `syntax`

数が多いためすべての例を挙げることはしませんが，いくつか紹介します．たとえば `instance` の場合，`local` を付けて登録したインスタンスがその `section` の内部限定になります．
-/

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

section
  -- local を付けてインスタンスを定義
  local instance : OfNat MyNat 0 where
    ofNat := MyNat.zero

  -- その section の中では使用できる
  #check (0 : MyNat)
end

-- section を抜けると使えなくなる
#check_failure (0 : MyNat)

/- ## 属性に対する `local`
属性付与の効果範囲を限定するためには，[`attribute`](./Attribute.md) コマンドを `local` で修飾するのではなく，`attribute` コマンドの中で `local` を使います．
-/

def MyNat.add (n m : MyNat) : MyNat :=
  match m with
  | zero => n
  | succ m => succ (MyNat.add n m)

theorem MyNat.zero_add (n : MyNat) : MyNat.add .zero n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [MyNat.add, ih]

section
  -- simp 属性をローカルに付与する
  attribute [local simp] MyNat.zero_add

  -- その section の中では使用できる
  #check (by simp : MyNat.add .zero .zero = .zero)
end

-- section を抜けると simp 補題が利用できなくなる
#check_failure (by simp : MyNat.add .zero .zero = .zero)
