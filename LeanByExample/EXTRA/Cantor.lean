/- # カントールの定理

カントールの定理(Cantor's theorem)とは、集合論における基本的な定理で、どんな集合 `X` に対しても、そのベキ集合 `P(X)` の方が真に大きいと主張するものです。Lean では集合論における集合そのものは普通扱わないのですが、型の世界でも同様のことが成り立ちます。

## 集合の大きさ比較

`X` が有限集合の場合、これは明らかです。`X` の要素数が `n` だとしたら、ベキ集合 `P(X)` の要素数は `2^n` になるからです。この定理の重要なところは、無限集合でも成り立つというところです。

その場合、無限集合の要素数を比較する必要がありますが、集合 `X, Y` に対して以下のように考えます。

* `X` と `Y` の間に全単射が存在するならば、`X` と `Y` の要素数は同じである。
* `X` から `Y` への全射が存在しないならば、`X` の要素数は `Y` より小さい。（単射による定義と同じ）
* `X` から `Y` への単射が存在しないならば、`X` の要素数は `Y` より大きい。(全射による定義と同じ)

`X` と `Y` の間にどのような写像が存在するかを見て、有限集合の場合の定義を拡張するわけです。

## 型の世界への翻訳

Lean は集合論の代わりに型理論を用いますが、型の世界でも同様のことが成り立ちます。

定理のステートメントに登場する集合 `X` のことは単に型 `X : Type u` と読み替えれば良いです。ベキ集合をどう表現するかですが、部分集合 `A ⊆ X` というものを「`X` の項 `x : X` に対して、それが `A` に属するかどうかを表す命題 `x ∈ A` を対応付けるもの」と読み替えることができて、関数型 `X → Prop` をベキ集合だと見做すことができます。
-/

/-- ベキ集合 -/
def Set (X : Type u) := X → Prop

/-
全射や単射は Lean に組み込みで定義されているものがあるので、これでカントールの定理のステートメントを述べることができます。
-/
namespace Show --#

open Function
set_option warn.sorry false --#

/-- カントールの定理の全射版 -/
theorem cantor_surjective (f : X → Set X) : ¬ Surjective f := by
  sorry

/-- カントールの定理の単射版 -/
theorem cantor_injective (f : Set X → X) : ¬ Injective f := by
  sorry

end Show --#
/- ## 集合の内包記法の用意

このまま証明をすることもできるのですが、このままだと記号が数学での表記と違い過ぎてわかりにくいので、記法を用意します。

まず `A : Set X` に対して `x ∈ A` と書けるようにします。
-/

instance : Membership X (Set X) where
  mem := fun A x => A x

-- テスト
#check
  let A : Set Nat := fun x => x < 5
  3 ∈ A

/-
次に、`{x : X ∣ P x}` という集合内包表記を用意します。これは [`macro_rules`](#{root}/Declarative/MacroRules.md) を使用してマクロとして用意します。
-/

/-- 述語から、それが内包によって定める部分集合を作る -/
def setOf (P : X → Prop) : Set X := P

/-- binder という構文カテゴリ。
これは変数束縛を表していて、
`{x : X | P x}` の `x : X` の部分とか
`{x ∈ X | P x}` の `x ∈ X` の部分とかを表している -/
declare_syntax_cat binder

/-- `{x : T | P x}` の `: T` の部分。
あってもなくても良いので `( )?` で囲う -/
syntax ident (" : " term)? : binder

/-- `{x ∈ T | P x}` の `∈ T` の部分。
あってもなくても良いので `( )?` で囲う -/
syntax ident (" ∈ " term)? : binder

/-- 集合の内包表記 -/
syntax "{" binder "|" term "}" : term

/-- `{x : T | P x}` と `{x ∈ T | P x}` の形の式を `setOf` の式に変換する -/
macro_rules
  | `({ $var:ident | $body:term }) => `(setOf (fun $var => $body))
  | `({ $var:ident : $ty:term | $body:term }) => `(setOf (fun ($var : $ty) => $body))
  | `({ $var:ident ∈ $s:term | $body:term }) => `(setOf (fun $var => $var ∈ $s ∧ $body))

-- テスト
#check
  let A : Set Nat := {x | x % 2 = 0}
  4 ∈ A

/- ## 全射版の証明

さて、それでは証明を書いていきましょう。まずは全射版からです。
-/

open Function

/-- カントールの定理の全射版 -/
theorem cantor_surjective (f : X → Set X) : ¬ Surjective f := by
  -- 仮に全射 `f : X → Set X` が存在したとする
  intro surjf

  -- ここで、自分自身の `f` の像に入らないような `x : X` を集めてきてそれを `T` とする
  let T : Set X := {x | x ∉ f x}

  -- `f` は全射だと仮定したので、`T` は `f` の像にあるはず
  -- そこで `f t = T` となる `t : X` を取る
  obtain ⟨t, ht⟩ := surjf T

  -- `t` が `T` に入るかどうかを考える。
  -- まず、`t ∈ T` だと仮定すると矛盾が得られるので `t ∉ T` がわかる
  have t_nmem : ¬ (t ∈ T) := by
    -- `t ∈ T` だと仮定する
    intro mem

    -- `T` の定義から、`t ∉ f t` であるはず
    have nmem : t ∉ f t := by
      dsimp [T, (· ∈ ·), setOf] at mem ⊢
      assumption

    -- しかし、`f t = T` であることから、これは `t ∉ T` を意味する
    rw [ht] at nmem

    -- これは矛盾
    contradiction

  -- `T = f t` であることから、これは `t ∉ f t` を意味し、
  -- すなわち `t ∈ T` ということになる。
  have t_mem : t ∈ T := by
    rw [← ht] at t_nmem
    dsimp [T, (· ∈ ·), setOf] at *
    assumption

  -- これは矛盾
  contradiction

/- ## 対角線論法

全射版カントールの定理の証明の中では、全射 `f : X → Set X` が存在すると仮定したときに、そこから `{x | x ∉ f x}` という集合を作ってくるところが核心でした。このテクニックは **対角線論法(diagonal argument)** と呼ばれます。

なんで「対角線」なのか疑問に思われたでしょうか？これは、図解してみるとわかります。

たとえば、`X = {x₁, x₂, x₃, x₄, x₅}` という有限集合を考えましょう。ここでどのような関数 `f : X → Set X` が与えられたとしても、`f` の像に入っていない部分集合 `T : Set X` を構成する具体的な手続きがあるかどうか考えてみましょう。

まず、`X` の部分集合は各 `xᵢ` を含んでいるか含んでいないかの長さ5のビット列で表すことができます。それぞれ `1` と `0` で表すことにすれば、`X` の部分集合は `[0, 1, 1, 1, 0]` のように表すことができることになります。そう考えると、各 `f : X → Set X` は２次元の表で表すことができます。

たとえば、常に `{x₁}` という１点集合を返す恒等関数 `f` は次の表と対応します。

![恒等関数の表](./Cantor/cantor.svg)
-/
