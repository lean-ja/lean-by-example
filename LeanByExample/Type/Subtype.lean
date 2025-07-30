/- # Subtype

`Subtype` は、大雑把に言えば型 `A : Type` の部分集合を表します。すなわちある述語 `p : A → Prop` があったとき、`Subtype p` は `A` の項であって `p` という性質を満たすようなものの全体を表します。
-/

-- 正の数を表す subtype
#check Subtype (fun n => n > 0)

/- [`{x : T // p x}`](#{root}/Parser/Subtype.md) という専用の構文が用意されていて、これで `Subtype` を表すことができます。 -/

-- 正の数を表す subtype
#check { n : Nat // n > 0 }

/- ## 実行時の性質

型 `A` の `Subtype` は実行時には `A` の項であるかのように振る舞います。言い換えれば、`{ x : A // p x}` の項は計算の実行時には `A` の項と同一視されます。これは、`Subtype` でラップしてもメモリアドレスが変わらないことから確認できます。
-/

unsafe def checkSubtype : IO Unit := do
  let x : Nat := 42
  let pos : { n : Nat // n > 0} := ⟨x, by omega⟩
  if ptrAddrUnsafe x != ptrAddrUnsafe pos then
    throw <| .userError "メモリアドレスが異なります。"

#eval checkSubtype

/- ## 用途

`Subtype` を使うと、ある型 `A` が `U` という型の一部を切り取ったものだということをコードで表現することができます。たとえば、自然数の型 `Nat` に対して、正の数だけを抜き出して正の整数の型 `Pos` を定義することを考えてみます。

このとき、`Subtype` を使わずに `Pos` を帰納型として以下のように定義することもできるのですが、こうすると `Pos` と `Nat` は実装上まったく無関係ということになってしまいます。
-/
namespace Hidden --#

inductive Pos where
  | one
  | succ (n : Pos)

end Hidden --#
/- その結果、`Nat` に対するコンパイラ上の演算の最適化の恩恵を受けることができなくなり、たとえば足し算が非常に遅くなります。

{{#include ./Subtype/Pos.md}}
-/
