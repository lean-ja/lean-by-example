/- # hygiene

`hygiene` オプションは、マクロ衛生機能を有効にするかどうかを制御します。

プログラミング言語に対して、マクロが **衛生的(hygienic)** であるとは、マクロ処理の過程で名前衝突の問題が発生しないことを指します。Lean のマクロはデフォルトで衛生的ですが、`hygiene` オプションは一時的にこれを無効にすることができます。
-/
section --#

/-- 定数関数を定義するマクロ -/
macro "const" e:term : term => `(fun x => $e)

def x : Nat := 42
def y : Nat := 42

-- マクロ衛生がきちんと働いているときの挙動
#guard (const x) 0 = 42
#guard (const y) 0 = 42

-- マクロ衛生を保つ機能を無効にする
set_option hygiene false

/-- マクロ衛生が無効になった定数関数マクロ -/
macro "const'" e:term : term => `(fun x => $e)

-- 引数の値が同じでも、識別子の名前によって値が変わるようになってしまった。
-- これはマクロの中で使用されている変数名も `x` であるため。
#guard (const' x) 0 = 0
#guard (const' y) 0 = 42

end --#
/- ## タクティクにおけるマクロ衛生

タクティクで導入される識別子についても、実行時の環境にある識別子と衝突しないようにする機能が Lean にはあります。
-/
section --#

macro "my_intro" : tactic => `(tactic| intro h)

example (P : Prop) : P → P := by
  my_intro

  -- `h : P` がマクロ展開によって導入されはするが、
  -- 死んでいるので使えない
  fail_if_success exact h

  assumption

-- マクロ衛生を保つ機能を無効にする
set_option hygiene false

macro "my_intro'" : tactic => `(tactic| intro h)

example (P : Prop) : P → P := by
  my_intro'

  -- `h : P` が使えてしまう
  exact h

end --#
/- また、(驚くべきことに)タクティクマクロの中で導入した識別子だけでなく、「参照した」識別子についても Lean が自動的に衝突を回避します。 -/
section --#

/-- exfalso タクティクを真似て自作したタクティク -/
macro "my_exfalso" : tactic => `(tactic| apply False.elim)

namespace Foo

  /-- `False.elim` とめっちゃよく似た名前の紛らわしい定理 -/
  theorem False.elim : 1 + 1 = 2 := by rfl

  example (_h : False) : 1 + 1 = 2 := by
    -- 普通に `apply` すると上の紛らわしい定理の方が使われてしまう
    apply False.elim

    done

  example (h : False) : 1 + 1 = 2 := by
    -- 実行した環境ではなくて宣言した環境における `False.elim` が使われる。
    -- 紛らわしい方の定理は使われない！
    my_exfalso

    show False
    contradiction

end Foo

-- マクロ衛生を保つ機能を無効にする
set_option hygiene false

/-- マクロ衛生が無効になったバージョンの `my_exfalso` -/
macro "my_exfalso'" : tactic => `(tactic| apply False.elim)

namespace Bar

  /-- `False.elim` とめっちゃよく似た名前の紛らわしい定理 -/
  theorem False.elim : 1 + 1 = 2 := by rfl

  example (_h : False) : 1 + 1 = 2 := by
    -- 紛らわしい方の `False.elim` が使われてしまう。
    my_exfalso'

    done

end Bar
end --#

/- ## 用途：定義すると同時に記法を使う

通常、[`notation`](#{root}/Declarative/Notation.md) コマンドなどによって導入された記法は定義の途中では使うことができません。定義が終了した後で記法を宣言するのが一般的です。
-/
namespace Ordinary

  inductive Nat.myle (n : Nat) : Nat → Prop where
    | refl : myle n n
    | step {m : Nat} : myle n m → myle n (m + 1)

  scoped notation:50 a:50 " ≤ₘ " b:50 => Nat.myle a b

end Ordinary
/- もし定義の途中で記法を使いたければ、[`hygiene`](#{root}/Option/Hygiene.md) オプションと [`local`](#{root}/Modifier/Local.md) 修飾子を利用して次のようにすれば可能です。 -/
section
  set_option hygiene false

  -- 定義の間だけ有効になるように記法を一時的に与える
  local notation:50 a:50 " ≤ₘ " b:50 => Nat.myle a b

  inductive Nat.myle (n : Nat) : Nat → Prop where
    | refl : n ≤ₘ n
    | step {m : Nat} : n ≤ₘ m → n ≤ₘ m + 1

end

-- 改めて記法を付与する
notation:50 a:50 " ≤ₘ " b:50 => Nat.myle a b

-- 通常通り証明が行える
example {n m k : Nat} (hnm : n ≤ₘ m) (hmk : m ≤ₘ k) : n ≤ₘ k := by
  induction hmk with
  | refl => assumption
  | step hmk ih =>
    apply Nat.myle.step
    assumption
