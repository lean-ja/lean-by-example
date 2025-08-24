/- # \#reduce
`#reduce` は、与えられた式をこれ以上簡約できなくなるまで簡約します。
-/

/-⋆-//-- info: 4 -/
#guard_msgs in --#
#reduce 1 + 3

/-⋆-//-- info: 4 -/
#guard_msgs in --#
#reduce (fun x => x + 1) 3

/- ## \#evalとの違い

これだけ見ると [`#eval`](./Eval.md) と同じですが、`#reduce` は式の評価ではなくて簡約なので、関数や型も渡すことができます。

以下は、関数を渡す例です。
-/

/-- 1を足すだけの関数 -/
def addOne (x : Nat) := x + 1

-- addOne が定義に展開されている
/-⋆-//-- info: fun x => x.succ -/
#guard_msgs in --#
#reduce addOne

-- 合成が計算できる
/-⋆-//-- info: fun x => x.succ.succ -/
#guard_msgs in --#
#reduce addOne ∘ addOne
/- また次は `#reduce` コマンドに型を渡す例です。 -/

/-- `Nat`に値を持つ`n`引数関数の型 -/
def Natural (n : Nat) : Type :=
  match n with
  | 0 => Nat
  | n + 1 => Natural n → Nat

-- 全く簡約されない
/-⋆-//-- info: Natural 0 -/
#guard_msgs in --#
#reduce Natural 0

/- ## 再帰除去

`#reduce` コマンドに再帰関数を渡してみると、出力結果に `.rec` などが含まれる複雑な式が返ってきます。特に、出力結果は再帰的ではありません。
-/

/-- 常にどんな値に対してもゼロを返す関数 -/
def zero {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: xs => zero xs

/-⋆-//--
info: fun xs => (List.rec ⟨0, PUnit.unit⟩ (fun head tail tail_ih => ⟨tail_ih.1, tail_ih⟩) xs).1
-/
#guard_msgs in --#
#reduce zero

/- これは、Lean が裏で **再帰除去(recursion elimination)** を行っているためです。

実際、Lean の型チェッカは再帰的な定義を受け付けないように設計されています。なぜかというと、再帰的な定義を（制限なしに）許すと矛盾が簡単に示せてしまうからです。
-/

/-- Lean の型チェッカが許すべきでない再帰関数の例 -/
unsafe def bad {P : Prop} : P := bad

-- 矛盾が示せてしまう
unsafe example : False := bad
