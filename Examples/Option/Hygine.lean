/- # hygine

`hygine` オプションは、マクロ衛生機能を有効にするかどうかを制御します。

プログラミング言語に対して、マクロが **衛生的(hygienic)** であるとは、マクロ処理の過程で名前衝突の問題が発生しないことを指します。Lean のマクロはデフォルトで衛生的ですが、`hygine` オプションは一時的にこれを無効にすることができます。
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
