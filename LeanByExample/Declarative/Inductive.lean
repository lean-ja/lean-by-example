/- # inductive
`inductive` コマンドは、**帰納型(inductive type)** を定義することができます。

帰納型とは、Lean においてユーザが新しい型を定義するための主要な方法です。帰納型はその型の項を得るための有限個の関数（コンストラクタ）を組み合わせることによって定まります。コンストラクタがこれから定義しようとしている型自身を引数に含むことも許されるので、帰納型は再帰的な構造を持つことができます。

## 帰納型の例

### 列挙型

帰納型の最も基本的な例は、次のような列挙型です。列挙型とは、固定された値のどれかを取るような型です。
-/
import Mathlib.SetTheory.Cardinal.Basic --#
/-- 真か偽のどちらかの値をとる型 -/
inductive MyBool where
  | true
  | false

#check (MyBool.true : MyBool)

/- 列挙型は、帰納型の中でもすべてのコンストラクタが引数を持たないような特別な場合といえます。-/

/- ### 再帰的なデータ構造

一般には、帰納型のコンストラクタは引数を持つことができます。コンストラクタの引数の型が定義しようとしているその帰納型自身であっても構いません。これにより、連結リストや二分木といった再帰的な構造を持つデータ型を定義することができます。-/

/-- 連結リスト -/
inductive LinkedList (α : Type) where
  /-- 空のリスト -/
  | nil

  /-- リスト `xs : LinkedList α` の先頭に `head : α` をつけたものはリスト -/
  | cons (head : α) (tail : LinkedList α)

/-- 2分木 -/
inductive BinTree (α : Type) where
  /-- 空の木 -/
  | empty

  /-- ノード `value : α` の左と右に木を付け加えたものは木 -/
  | node (value : α) (left right : BinTree α)

/- ### 帰納族

ある添字集合 `Λ : Type` の要素 `λ : Λ` のそれぞれに対して、型 `T λ : Sort u` を独立した型として定義することができます。簡単な例として、長さを型の情報として持つリストがあります。
-/

/-- 長さを型の情報として持つリスト -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : Vec α (n + 1)

/- これで帰納型の族 `{Vec α 0, Vec α 1, Vec α 2, …}` を定義したことになります。このように定義される帰納型の族を **帰納族(inductive family)** と呼びます。

`inductive` コマンドはパラメータと添字(index)を区別するため、次のように書くとエラーになることに注意してください。
-/

/-⋆-//--
error: inductive datatype parameter mismatch
  0
expected
  n
-/
#guard_msgs in --#
inductive BadVec (α : Type) (n : Nat) : Type where
  | nil : BadVec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : BadVec α (n + 1)

/- このようにコードを書くと `n` はパラメータとして扱われます。パラメータは、各コンストラクタの返り値の型に一様に現れなくてはいけません。
したがって、`nil` の右辺には `BadVec α 0` ではなく `BadVec α n` が来なければならないというエラーが出ているわけです。実際に、このエラーはコンストラクタの返り値の型を変更すれば消すことができます。
-/

/-- 良くない方法でエラーを消した `BadVec` -/
inductive BadVec' (α : Type) (n : Nat) : Type where
  | nil : BadVec' α n
  | cons (a : α) (v : Vec α n) : BadVec' α n

#check (BadVec'.nil : BadVec' Nat 3)

/- しかし、元々の `Vec` とは似て非なるものになってしまいます。上記の `BadVec'` では、`nil : BadVec α 0` だけでなく `nil : BadVec α 1` や `nil : BadVec α 2` なども存在すると宣言したことになってしまいます。-/

/- ### 帰納的述語
帰納型を使って命題や述語を定義することもできます。作為的ではありますが簡単な例として、自然数が偶数であることを表す命題が挙げられます。
-/

/-- 自然数が偶数であることを表す帰納的述語 -/
inductive MyEven : Nat → Prop where
  | zero : MyEven 0
  | add_two : ∀ n, MyEven n → MyEven (n + 2)

/- この場合 `inductive` コマンドを使用せずに、`def` を使って再帰関数として定義しても同じことができます。 -/

/-- 自然数が偶数であることを表す再帰関数 -/
def even : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => even n

/- 両者の違いは何でしょうか？双方にメリットとデメリットがあります。

再帰関数として定義するメリットとして、計算可能になることが挙げられます。再帰関数として定義されていれば [`#eval`](#{root}/Diagnostic/Eval.md) コマンドなど、Lean に組み込まれた機能を使って計算を行うことができます。一方で帰納的述語として定義されていると、計算をさせるための準備をこちらで行う必要があります。-/

-- すぐに計算できる
#guard even 4

/-⋆-//--
error: failed to synthesize
  Decidable (MyEven 4)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in --#
#eval MyEven 4

/-
帰納的述語として定義するメリットとしては、再帰が停止することを保証しなくて良いことが挙げられます。実際、帰納的述語は本質的に停止する保証がない再帰的な操作でも扱うことができます。以下は、少し複雑ですがプログラムの BigStep 意味論を表現する例です。[^hitchhiker]
-/

/-- 変数。ここでは簡単のために、すべての文字列が変数として存在するものとする -/
abbrev Variable := String

/-- プログラムの状態。すべての変数の値を保持したもの。
ここでは簡単にするために、変数の値はすべて自然数だとしている。 -/
def State := Variable → Nat

/-- `1 + x` のような算術式。変数の値を決めるごとに値が決まる。-/
def Arith := State → Nat

/-- 抽象化された単純なプログラミング言語のプログラム -/
inductive Stmt : Type where
  /-- 何もしないコマンド -/
  | skip
  /-- `x := a` のような代入文。-/
  | assign (v : Variable) (expr : Arith)
  /-- 2つのコマンドを続けて実行する。`;;` で表される。-/
  | seq (S T : Stmt)
  /-- while 文 -/
  | whileDo (B : State → Prop) (S : Stmt)

@[inherit_doc] infix:60 ";; " => Stmt.seq

-- 技術的な理由で必要
set_option quotPrecheck false in

/-- 状態 `s : State` があったとき、変数 `x` に対してだけ値を更新したものを表す記法 -/
notation s:70 "[" x:70 "↦" n:70 "]" => (fun v ↦ if v = x then n else s v)

open Stmt

/-- プログラムの BigStep 意味論。`BigStep c s t` は、
プログラム `c` を状態 `s` の下で実行すると状態が `t` になって停止することを表す。
-/
inductive BigStep : Stmt → State → State → Prop where
  /-- skip コマンドの意味論。-/
  | skip (s : State) : BigStep skip s s

  /-- 代入文 `x := a` の実行前に状態が `s` であったなら、
  代入文の実行後には状態は変数 `x` についてだけ更新される。-/
  | assign (x : Variable) (a : State → Nat) (s : State) :
    BigStep (assign x a) s (s[x ↦ a s])

  /-- seq コマンドの意味論。-/
  | seq {S T : Stmt} {s t u : State} (hS : BigStep S s t) (hT : BigStep T t u) :
    BigStep (S;; T) s u

  /-- while 文の、条件式が真のときの意味論。
  `whileDo B S` は、開始時に `B` が成り立っているなら、
  `S` を実行してから `whileDo B S` を実行するのと同じ意味になる。-/
  | while_true {B S s t u} (hcond : B s) (hbody : BigStep S s t)
    (hrest : BigStep (whileDo B S) t u) : BigStep (whileDo B S) s u

  /-- while 文の、条件式が偽のときの意味論。-/
  | while_false {B S s} (hcond : ¬ B s) : BigStep (whileDo B S) s s

/- 「プログラムを評価する」という操作は `while` 文の評価が終わらない可能性があるため、再帰関数として定義することができません。そのため上記の BigStep 意味論の例は帰納的述語が真に有用なケースであるといえます。-/

/- ## 帰納型の仕様

### 再帰子

`inductive` コマンドで帰納型 `T` を定義すると、**再帰子(recursor)** `T.rec` が自動生成されます。再帰子は [`induction`](#{root}/Tactic/Induction.md) タクティクで使用されるほか、[`[induction_eliminator]`](#{root}/Attribute/InductionEliminator.md) 属性にも関係があります。

たとえば列挙型である `Bool` の場合、再帰子は次のようになっています。
-/

/-⋆-//--
info: recursor Bool.rec.{u} : {motive : Bool → Sort u} → motive false → motive true → (t : Bool) → motive t
-/
#guard_msgs in --#
#print Bool.rec

/- この再帰子の型をよく見ると、`Bool` から型 `motive _` への依存関数 `(t : Bool) → motive t` を構成する手段を提供していることがわかります。

[`Nat`](#{root}/Type/Nat.md) の場合はもっとわかりやすいです。
-/

/-⋆-//--
info: recursor Nat.rec.{u} : {motive : ℕ → Sort u} →
  motive Nat.zero → ((n : ℕ) → motive n → motive n.succ) → (t : ℕ) → motive t
-/
#guard_msgs in --#
#print Nat.rec

/- `Nat` から型 `motive _` への依存関数 `(t : Nat) → motive t` を構成する手段を提供しているのは同じなのですが、よく見ると帰納法の原理そのものの形をしています。

型 `motive t` が棲んでいる宇宙 `Sort u` に `Prop` を代入してみましょう。このとき `motive Nat.zero` 型の引数というのは、命題 `motive Nat.zero : Prop` の証明にほかならず、`(n : ℕ) → motive n → motive n.succ` 型の引数というのは、命題 `∀ n, motive n → motive (n + 1)` の証明にほかなりません。この条件の下で関数 `(t : Nat) → motive t` つまり `∀ t, motive t` の証明が得られると主張しているのですから、帰納法の原理そのものであることがわかります。 -/

/- ### noConfusion

帰納型のコンストラクタは必ず単射になり、異なるコンストラクタの像は決して重なりません。このルールは、`injection` タクティクで利用することができます。
-/

/-- Peano の公理によって定義された自然数 -/
inductive MyNat : Type where
  | zero
  | succ (n : MyNat)

/-- コンストラクタの像は重ならない -/
example (n : MyNat) : .succ n ≠ MyNat.zero := by
  intro h
  injection h

/-- コンストラクタは必ず単射である -/
example (n m : MyNat) : MyNat.succ n = MyNat.succ m → n = m := by
  intro h
  injection h

/- [`show_term`](#{root}/Tactic/ShowTerm.md) を使用して証明項を出してみると、`injection` タクティクにより `MyNat.noConfusion` という定理が呼ばれていることがわかります。 -/

/-⋆-//-- info: Try this: MyNat.noConfusion h fun n_eq => n_eq -/
#guard_msgs in --#
example (n m : MyNat) (h : MyNat.succ n = MyNat.succ m) : n = m := show_term by
  injection h

/- ## strictly positive 要件 { #StrictlyPositiveRequirement }

帰納型を定義しようとした際に、次のようなエラーになることがあります。
-/

/-⋆-//--
error: (kernel) arg #1 of 'Foo.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in --#
inductive Foo where
  | mk (f : Foo → Nat)

/- エラーメッセージには「`Foo.mk` の引数の中に、定義しようとしている型が non positive に現れている」と書かれています。この positive とは、引数における位置のことで、一般に関数型 `X → Y` があるとき `X` は **負の位置(negative position)** であり、`Y` は **正の位置(positive position)** であると呼びます。ただし関数の型が入れ子になっていると正負が変わります。たとえば `(X → Y) → Z` という型の場合、`X` は負の位置の負の位置にあるので、正の位置と見なされます。上記の `Foo` のコンストラクタには `Foo` 自身が現れていますが、コンストラクタの引数の型の中で正の位置に現れていないので、それがルール違反であるとエラーメッセージは言っているわけです。

次の例では、`Bar` のコンストラクタの引数の型の中で `Bar` 自身が正の位置に現れていますが、これも同じエラーになります。
-/

/-⋆-//--
error: (kernel) arg #1 of 'Bar.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in --#
inductive Bar where
  | mk (f : (Bar → Nat) → Nat)

/- どの `→` から見ても正の位置にあるときには狭義の正の位置(strictly positive position)と呼ばれるのですが、Lean は実際には狭義の正の位置でなければ定義を拒否します。帰納型 `T` のコンストラクタの引数の中に `T` 自身が現れる場合、狭義の正の位置つまり `A → T` の形で現れるのは許容されますが `T → A` の形で現れるのは許されません。これを strictly positive 要件と本書では呼びます。

strictly positive 要件に違反するような帰納型を仮に定義できたとすると、矛盾が導かれてしまいます。[`unsafe`](#{root}/Modifier/Unsafe.md) 修飾子で実際に試してみましょう。[^stpos] -/

-- 任意に型 A が与えられたとして固定する
opaque A : Type

/-- strictly positive 要件を破っている帰納型 -/
unsafe inductive Bad where
  | mk (f : Bad → A)

section
  /- ## A が空の場合

  `A` が空なら、`A` は `False` と同じなので矛盾が導かれる。
  -/

  unsafe def selfApply (b : Bad) : A :=
    match b with
    | Bad.mk f => f b

  -- A の項が A の情報を使わずに構成できてしまった
  unsafe def ω : A := selfApply (Bad.mk selfApply)

  /-- `A` が空なら矛盾が導かれる -/
  unsafe example [IsEmpty A] : False :=
    IsEmpty.false ω
end

section
  /- ## A に２つ以上の要素があるとき -/

  /-- `Bad` と `Bad → A` の間に全単射がある -/
  unsafe def equiv : Bad ≃ (Bad → A) where
    toFun := fun ⟨f⟩ => f
    invFun := Bad.mk
    left_inv := by
      intro ⟨f⟩
      rfl
    right_inv := by
      intro f
      rfl

  open scoped Cardinal

  unsafe example [Nontrivial A] : False := by
    -- `Bad` と `Bad → A` は全単射があるので濃度(`#`)が同じ
    have h : # Bad = # (Bad → A) :=
      Cardinal.mk_congr equiv

    -- 特に、`# Bad = # A ^ # Bad` が成り立つ
    replace h : # Bad = #A ^ # Bad := by
      simpa [Cardinal.mk_pi, Cardinal.prod_const, Cardinal.lift_id] using h

    -- しかしカントール(Cantor)の定理により、`# A ≥ 2` ならば
    -- `# Bad < # A ^ # Bad` が成り立つ
    have : # Bad < #A ^ # Bad := by
      apply Cardinal.cantor' (a := # Bad) (b := # A)
      rw [Cardinal.one_lt_iff_nontrivial]
      infer_instance

    -- これは矛盾
    apply ne_of_lt this h
end

/- ここで、`ω` の定義が無限ループに陥っていることは指摘する価値があります。 -/

-- ω を簡約すると ω 自身が出てくる
-- つまり無限ループしている
/-⋆-//--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in --#
#reduce ω

/- [^hitchhiker]: [The Hitchhiker’s Guide to Logical Verification](https://github.com/blanchette/interactive_theorem_proving_2024) を参考にいたしました。
[^stpos]: 以下の証明は、Lean 公式 Zulip の strictly positive requirement というトピックで [Markus Himmel さんが示した証明](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/strictly.20positive.20requirement/near/497174984)を参考にしています。
-/
