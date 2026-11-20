/- # unsafe

`unsafe` は、Lean の健全性ルールを破るような操作を許可するのに使う修飾子です。`unsafe` を使用すると、矛盾を導きうるような危険な操作が許可されます。
-/

/- ## unsafe が破るルールの例

### strictly positive 要件

次のような帰納型は [strictly positive 要件](#{root}/Declarative/Inductive.md#StrictlyPositiveRequirement)というLeanのルールに反するのでエラーになり、定義することができません。
-/
namespace Playground --#

--#--
/--
error: (kernel) arg #1 of 'Playground.Bad.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs (error) in
--#--
inductive Bad where
  | mk : (Bad → Bad) → Bad

end Playground --#
/- `unsafe` で修飾すれば定義が通るようになります。 -/

unsafe inductive Bad where
  | mk : (Bad → Bad) → Bad

/- ### 再帰関数の停止性

通常再帰関数は停止することが証明できなければ定義ができませんが、`unsafe` を使用するとこのエラーを無視することができます。
-/

variable {α : Type}

/-- 数列 `as` が `start` 以降で最初に `some _` になる値を返す -/
unsafe def findSome (as : Nat → Option α) (start : Nat) : α :=
  match as start with
  | some x => x
  | none => findSome as (start + 1)

unsafe example : False := by
  -- α が Empty でも許されるので、矛盾を示すことができる
  let _ : Empty := findSome (α := Empty) (as := fun n => none) 0
  grind only

/- ## ptrAddrUnsafe { #ptrAddrUnsafe }

`ptrAddrUnsafe` 関数は、値のメモリ上での位置を返す関数ですが、`unsafe` で修飾されています。 -/

/-- info: unsafe opaque ptrAddrUnsafe.{u} : {α : Type u} → α → USize -/
#guard_msgs in --#
#print ptrAddrUnsafe

/- これは、`ptrAddrUnsafe` が **参照透過性(referential transparency)** を壊してしまうからです。参照透過性とは、「引数の値が同じならば関数の値も同じ」という性質です。`ptrAddrUnsafe` は等しい引数でも異なる値を返すことがあります。 -/

/-- info: true -/
#guard_msgs in --#
#eval show Bool from Id.run do
  let u := ptrAddrUnsafe ([1, 2, 3])
  let v := ptrAddrUnsafe ([1, 2] ++ [3])

  -- 引数の値は同じだが
  assert! [1, 2, 3] == [1, 2] ++ [3]

  -- 返り値が異なる!
  return u != v

/- ## Functional but in-place { #FBIP }
`unsafe` が付与されていない通常の関数は参照透過性を持ち、したがって特に Lean ではグローバル変数の値を変更することは通常できません。 -/

-- foo という変数を定義する
def foo := "hello"

-- 再定義しようとするとエラーになる
/-- error: `foo` has already been declared -/
#guard_msgs in --#
def foo := "hello world"

/-
しかし、ローカル変数は破壊的に変更することができます。
-/

/-- フィボナッチ数列を計算する -/
def fibonacci (n : Nat) : Array Nat := Id.run do
  -- 可変な配列 `fib` を宣言する
  let mut fib : Array Nat := Array.mkEmpty n
  fib := fib.push 0
  fib := fib.push 1
  for i in [2:n] do
    -- 更新前の配列 `fib` のメモリアドレスを取得
    let old := unsafe ptrAddrUnsafe fib

    -- `fib` を更新
    fib := fib.push (fib[i-1]! + fib[i-2]!)

    -- 更新後のメモリアドレスを取得
    let new := unsafe ptrAddrUnsafe fib

    -- メモリアドレスが一致する
    assert! old = new
  return fib

-- 値がコピーされていれば panic するはずだが...?
/-- info: #[0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377] -/
#guard_msgs in --#
#eval fibonacci 15

/- なぜこのようなことができるのかというと、Lean が値の不要なコピーを行わないからです。具体的には、Lean は **参照カウント** がちょうど１であるような値を更新する際に、コピーして新しい値を生成する代わりに破壊的変更を行います。これを指して、Lean 言語のパラダイムのことを **Functional but in-place** と呼ぶことがあります。
-/
