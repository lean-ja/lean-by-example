/- # unsafe

`unsafe` は、Leanのルールを破るような操作を許可するのに使う修飾子です。

たとえば、次のような帰納型は [strictly positive 要件](#{root}/Declarative/Inductive.md#StrictlyPositiveRequirement)というLeanのルールに反するのでエラーになり、定義することができません。
-/

/-⋆-//--
error: (kernel) arg #1 of 'Bad.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in --#
inductive Bad where
  | mk : (Bad → Bad) → Bad

/- `unsafe` で修飾すれば定義が通るようになります。 -/

unsafe inductive Bad where
  | mk : (Bad → Bad) → Bad

/- ## unsafe が付与された関数

Lean のライブラリには `unsafe` が付与された関数がいくつも存在します。

たとえば `ptrAddrUnsafe` 関数は、値のメモリ上での位置を返す関数ですが、`unsafe` で修飾されています。 -/

/-⋆-//-- info: unsafe opaque ptrAddrUnsafe.{u} : {α : Type u} → α → USize -/
#guard_msgs in --#
#print ptrAddrUnsafe

/- これは、`ptrAddrUnsafe` が **参照透過性(referential transparency)** を壊してしまうからです。参照透過性とは、「引数の値が同じならば関数の値も同じ」という性質で、Lean では全ての関数は参照透過であるべきというルールを課せられています。-/

/-⋆-//-- info: true -/
#guard_msgs in --#
#eval show Bool from Id.run do
  let u := ptrAddrUnsafe ([1, 2, 3])
  let v := ptrAddrUnsafe ([1, 2] ++ [3])

  -- 引数の値は同じだが
  assert! [1, 2, 3] == [1, 2] ++ [3]

  -- 返り値が異なる!
  return u != v
