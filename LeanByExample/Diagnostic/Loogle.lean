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
  [apply] #check Nat.add_zero --  (n : ℕ) : n + 0 = n
  ⏎
  [apply] #check instNeZeroNatHAdd --  {n m : ℕ} [h : NeZero n] : NeZero (n + m)
  ⏎
  [apply] #check instNeZeroNatHAdd_1 --  {n m : ℕ} [h : NeZero m] : NeZero (n + m)
  ⏎
  [apply] #check Nat.zero_add --  (n : ℕ) : 0 + n = n
  ⏎
  [apply] #check Nat.add_one_ne_zero --  (n : ℕ) : n + 1 ≠ 0
  ⏎
  [apply] #check Nat.zero_ne_add_one --  (n : ℕ) : 0 ≠ n + 1
-/
#guard_msgs in --#
#loogle "Nat", "zero", "add"

/- ### 特定の定数・関数が登場するか

たとえば `List.foldl` という関数についてどのような補題が存在するか知りたいとします。このような場合、`List.foldl` が定理の中で言及されているような定理を検索したいですが、これはそのまま識別子を与えることで検索可能です。
-/

/-⋆-//--
info: Loogle Search Results
  [apply] #check List.foldl --  {α : Type u} {β : Type v} (f : α → β → α) (init : α) : List β → α
  Folds a function over a list from the left, accumulating a value starting with `init`. The
  accumulated value is combined with the each element of the list in order, using `f`.
  ⏎
  Examples:
   * `[a, b, c].foldl f z  = f (f (f z a) b) c`
   * `[1, 2, 3].foldl (· ++ toString ·) "" = "123"`
   * `[1, 2, 3].foldl (s!"({·} {·})") "" = "((( 1) 2) 3)"`
  ⏎
  ⏎
  [apply] #check List.foldl_nil --  {α✝ : Type u_1} {β✝ : Type u_2} {f : α✝ → β✝ → α✝} {b : α✝} : List.foldl f b [] = b
  ⏎
  [apply] #check List.foldl_cons --  {α : Type u} {β : Type v} {a : α} {l : List α} {f : β → α → β} {b : β} : List.foldl f b (a :: l) = List.foldl f (f b a) l
  ⏎
  [apply] #check List.id_run_foldlM --  {β : Type u_1} {α : Type u_2} {f : β → α → Id β} {b : β} {l : List α} : (List.foldlM f b l).run = List.foldl f b l
  ⏎
  [apply] #check List.foldl_eq_foldr_reverse --  {α : Type u_1} {β : Type u_2} {l : List α} {f : β → α → β} {b : β} : List.foldl f b l = List.foldr (fun x y => f y x) b l.reverse
  ⏎
  [apply] #check List.foldl_reverse --  {α : Type u_1} {β : Type u_2} {l : List α} {f : β → α → β} {b : β} : List.foldl f b l.reverse = List.foldr (fun x y => f y x) b l
-/
#guard_msgs in --#
#loogle List.foldl

/- ### 型による検索

探したい定理・関数が持っているはずの型で検索することができます。たとえば `List.map` という関数をどわすれしたとしましょう。このとき、`(α → β) → List α → List β` という型を持つ関数を探すことで、`List.map` にたどり着くことができます。それには型変数の部分をメタ変数にして検索クエリを作ります。
-/

/-⋆-//--
info: Loogle Search Results
  [apply] #check List.map --  {α : Type u_1} {β : Type u_2} (f : α → β) (l : List α) : List β
  Applies a function to each element of the list, returning the resulting list of values.
  ⏎
  `O(|l|)`.
  ⏎
  Examples:
  * `[a, b, c].map f = [f a, f b, f c]`
  * `[].map Nat.succ = []`
  * `["one", "two", "three"].map (·.length) = [3, 3, 5]`
  * `["one", "two", "three"].map (·.reverse) = ["eno", "owt", "eerht"]`
  ⏎
  ⏎
  [apply] #check List.modifyHead --  {α : Type u} (f : α → α) : List α → List α
  Replace the head of the list with the result of applying `f` to it. Returns the empty list if the
  list is empty.
  ⏎
  Examples:
   * `[1, 2, 3].modifyHead (· * 10) = [10, 2, 3]`
   * `[].modifyHead (· * 10) = []`
  ⏎
  ⏎
  [apply] #check List.mapTR --  {α : Type u} {β : Type v} (f : α → β) (as : List α) : List β
  Applies a function to each element of the list, returning the resulting list of values.
  ⏎
  `O(|l|)`. This is the tail-recursive variant of `List.map`, used in runtime code.
  ⏎
  Examples:
  * `[a, b, c].mapTR f = [f a, f b, f c]`
  * `[].mapTR Nat.succ = []`
  * `["one", "two", "three"].mapTR (·.length) = [3, 3, 5]`
  * `["one", "two", "three"].mapTR (·.reverse) = ["eno", "owt", "eerht"]`
  ⏎
  ⏎
  [apply] #check List.modify --  {α : Type u} (l : List α) (i : ℕ) (f : α → α) : List α
  Replaces the element at the given index, if it exists, with the result of applying `f` to it. If the
  index is invalid, the list is returned unmodified.
  ⏎
  Examples:
   * `[1, 2, 3].modify 0 (· * 10) = [10, 2, 3]`
   * `[1, 2, 3].modify 2 (· * 10) = [1, 2, 30]`
   * `[1, 2, 3].modify 3 (· * 10) = [1, 2, 3]`
  ⏎
  ⏎
  [apply] #check List.mapTR.loop --  {α : Type u} {β : Type v} (f : α → β) : List α → List β → List β
  ⏎
  [apply] #check List.map_eq_mapTR --  : @List.map = @List.mapTR
-/
#guard_msgs in --#
#loogle (?a → ?b) → List ?a → List ?b

/- ### パターンによる検索

パターンで検索することもできます。たとえば、`n * m = 0 ↔ n = 0 ∨ m = 0` を主張する定理の名前が知りたいとしましょう。このとき、定理の中に出現するべきパターンから検索することができます。
-/

/-⋆-//--
info: Loogle Search Results
  [apply] #check Nat.mul_eq_zero --  {m n : ℕ} : n * m = 0 ↔ n = 0 ∨ m = 0
-/
#guard_msgs in --#
#loogle "Nat", "mul", (_ * _ = 0), (_ = 0 ∨ _ = 0)
