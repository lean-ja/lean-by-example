/- # fun_cases

`fun_cases` は、関数定義に応じて場合分けを行うためのタクティクです。

たとえば以下の例では、`swapHead` はリストに対して「空か、シングルトンか、そのほか」で場合分けをして定義されています。一方でリストは再帰的なデータ型としては「空か、そのほか」で定義されているため、[`cases`](./Cases.md) タクティクで普通に場合分けをしようとすると場合分けの分岐が合いません。`fun_cases` を使うと、関数定義で使用された場合分けを再利用することができます。
-/
variable {α : Type}

/-- リストの先頭２要素を入れ替える -/
@[simp]
def swapHead (xs : List α) : List α :=
  match xs with
  | [] => []
  | [x] => [x]
  | x :: y :: zs => y :: x :: zs

example (l : List α) : swapHead (swapHead l) = l := by
  fun_cases swapHead l <;> simp

-- `fun_cases` を使用しなかった場合、場合分けの手間が増える
example (l : List α) : swapHead (swapHead l) = l := by
  cases l with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys => simp

/- ## 舞台裏

Lean で関数 `f` を定義すると `f.fun_cases` という名前の補助的な定理が自動生成されます。`fun_cases` タクティクは、この補助定理を使用して場合分けを行っています。[`cases`](./Cases.md) タクティクでも、`using` で明示的に指定すれば `fun_cases` と同様のことができます。
-/

example (l : List α) : swapHead (swapHead l) = l := by
  cases l using swapHead.fun_cases <;> simp
