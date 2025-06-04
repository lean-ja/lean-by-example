/- # \#loogle

`#loogle` コマンドは、Lean で定理や関数を探すための検索エンジンである、[Loogle](https://loogle.lean-lang.org/) を利用した検索をエディタ上で行うためのコマンドです。Loogle で使用できるのと同様の検索クエリが使用できます。

[`#find`](#{root}/Diagnostic/Find.md) と似ていますが、`#find` と違って `#loogle` はAPIを利用するだけなのでより高速に動作します。

## 検索クエリの書き方

### 名前に特定の文字列が含まれるかどうか

二重引用符 `"` で文字列を囲って与えると、補題の名前にその文字列が含まれるような補題や、関数名にその文字列が含まれるような関数を検索します。

たとえば、仮に `Nat.add_zero : ∀ n : Nat, n + 0 = 0` の名前をどわすれして、思い出したいとしましょう。ここで「整数の、ゼロの和に関する定理」というところまで思い出せるのであれば、定理名に入っていそうな文字列を与えることで検索に引っかけることができます。
-/
import LeanSearchClient.LoogleSyntax

/-⋆-//--
info: Loogle Search Results
• #check Nat.add_zero
• #check instNeZeroNatHAdd
• #check instNeZeroNatHAdd_1
• #check Nat.zero_add
• #check Nat.add_one_ne_zero
• #check Nat.zero_ne_add_one
-/
#guard_msgs in --#
#loogle "Nat", "zero", "add"

/- ### 特定の定数・関数が登場するか

たとえば `List.foldl` という関数についてどのような補題が存在するか知りたいとします。このような場合、`List.foldl` が定理の中で言及されているような定理を検索したいですが、これはそのまま識別子を与えることで検索可能です。
-/

/-⋆-//--
info: Loogle Search Results
• #check List.foldl
• #check List.foldl_nil
• #check List.foldl_cons
• #check List.id_run_foldlM
• #check List.foldl_eq_foldr_reverse
• #check List.foldl_reverse
-/
#guard_msgs in --#
#loogle List.foldl

/- ### 型による検索

探したい定理・関数が持っているはずの型で検索することができます。たとえば `List.map` という関数をどわすれしたとしましょう。このとき、`(α → β) → List α → List β` という型を持つ関数を探すことで、`List.map` にたどり着くことができます。それには型変数の部分をメタ変数にして検索クエリを作ります。
-/

/-⋆-//--
info: Loogle Search Results
• #check List.modifyHead
• #check List.map
• #check List.mapTR
• #check List.modify
• #check List.mapTR.loop
• #check List.map_eq_mapTR
-/
#guard_msgs in --#
#loogle (?a → ?b) → List ?a → List ?b

/- ### パターンによる検索

パターンで検索することもできます。たとえば、`n * m = 0 ↔ n = 0 ∨ m = 0` を主張する定理の名前が知りたいとしましょう。このとき、定理の中に出現するべきパターンから検索することができます。
-/

/-⋆-//--
info: Loogle Search Results
• #check Nat.mul_eq_zero
-/
#guard_msgs in --#
#loogle "Nat", "mul", (_ * _ = 0), (_ = 0 ∨ _ = 0)
