/- # \#reduce
`#reduce` は、与えられた式をこれ以上簡約できなくなるまで簡約します。
-/

/-- info: 4 -/
#guard_msgs in #reduce 1 + 3

/-- info: 4 -/
#guard_msgs in #reduce (fun x => x + 1) 3

/- これだけ見ると [`#eval`](./Eval.md) と同じですが、`#reduce` は式の評価ではなくて簡約なので、関数や型も渡すことができます。-/

def addOne (x : Nat) := x + 1

-- addOne が定義に展開されている
/-- info: fun x => x.succ -/
#guard_msgs in #reduce addOne

-- 合成が計算できる
/-- info: fun x => x.succ.succ -/
#guard_msgs in #reduce addOne ∘ addOne
