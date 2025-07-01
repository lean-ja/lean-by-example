/-
# Inhabited
`Inhabited` は、ある型にデフォルトの項があることを示す型クラスです。

`Inhabited` のインスタンスである型は、`default` という項を持ちます。
-/
section
  variable {α : Type} [Inhabited α]

  #check (default : α)
end
/- `Inhabited` の注意すべき使われ方として、クラッシュする関数の返り値として呼ばれるというものがあります。

たとえば `a : Array` に対して `i` 番目の要素を取り出す処理を考えます。`i` 番目の要素が存在するとは限らないので、例外の処理が必要です。一つの方法は、「`i` 番目の要素がなければエラーにする」というものです。
-/

def get {α : Type} [Inhabited α] (a : Array α) (i : Nat) : α :=
  if h : i < a.size then
    a[i]'h
  else
    panic! "index out of bounds"

/- 何気ない定義のように見えますが、この定義には `Inhabited α` が必要です。`panic!` でプログラムをクラッシュさせているのですが、このときに `α` が空でないことが要求されています。-/

/-⋆-//--
error: failed to synthesize
  Inhabited α

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in --#
def get' {α : Type} (a : Array α) (i : Nat) : α :=
  if h : i < a.size then
    a[i]'h
  else
    panic! "index out of bounds"

/- これは Lean が定理証明支援系としてもプログラミング言語としても使えるようにするための技術的な制約からくる仕様です。もし空の型を返してプログラムがクラッシュすることが許されたとすると、「空の型は `False` に等しい」ので、クラッシュするプログラムを `False` の証明として扱える可能性が生じてしまいます。
-/
