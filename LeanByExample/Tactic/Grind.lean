/- # grind

`grind` は、現代の SMT ソルバにインスパイアされた証明自動化タクティクです。[^reference]

非常に強力であり、時に驚くほどギャップのある証明を自動で完了させることができます。[^impressive]
-/

/-- 階乗関数 -/
@[grind]
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

@[inherit_doc factorial]
notation:max n "!" => factorial n

/-- 階乗関数の値は１以上 -/
theorem one_le_factorial (n : Nat) : 1 ≤ n ! := by
  fun_induction factorial <;> grind

-- `n !` を見かけたら `one_le_factorial` を利用するよう `grind` に指示
grind_pattern one_le_factorial => n !

/-- Pascal の三角形 -/
def pascal (a b : Nat) : Nat :=
  match a, b with
  | _, 0 => 1
  | 0, _ + 1 => 1
  | a + 1, b + 1 => pascal (a + 1) b + pascal a (b + 1)

/-- Pascal の三角形の性質 -/
theorem pascal_le_factorial (a b : Nat) : pascal a b ≤ (a + b)! := by
  fun_induction pascal <;> grind

/- ## 動作原理の概要

`grind` タクティクの動作原理を理解するには、仮想的な黒板を思い浮かべると良いでしょう。
新しい等式や不等式を見つけるたびに、`grind` はその事実を黒板に書き込んでいきます。
`grind` は「最初に結論の否定を仮定して矛盾を示す」ことでゴールを示すように設計されているため、最初に黒板に書き込むのは示したいゴールの仮定と結論の否定です。
-/

set_option trace.grind.assert true in

/-⋆-//--
trace: [grind.assert] P
[grind.assert] ¬P
-/
#guard_msgs in --#
example (P : Prop) (h : P) : P := by
  grind

/- そうやって黒板に事実を書き込みながら、`grind` は同値類（equivalence class、互いに等しいもの同士のグループのこと）を管理していて、等しいと分かった同値類をマージしていきます。そして最終的に `True` のグループと `False` のグループをマージする（つまり、矛盾を示す）ことでゴールを閉じます。 -/

set_option trace.grind.eqc true in

/-⋆-//--
trace: [grind.eqc] P = True
[grind.eqc] P = False
-/
#guard_msgs in --#
example (P : Prop) (h : P) : P := by
  grind

/-
以上の「仮想的な黒板による同値類の管理」が中核的な動作原理で、さらに `grind` には以下のようなエンジンが組み込まれています。

* 合同閉包(congruence closure)
* E-マッチング(E-matching)
* 制約伝播(Constraint Propagation)
* サテライトソルバー(特定の代数系に対するソルバー群)
-/

/- ## 注意: 選択原理の使用

`grind` は「最初に結論を否定して矛盾を示すことでゴールを閉じる」という原理で動くため、必要がない場合であっても[選択原理](#{root}/Declarative/Axiom.md#ClassicalChoice)を使用します。
-/

theorem easy_theorem (P : Prop) (h : P) : P := by
  grind

/-⋆-//-- info: 'easy_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in --#
#print axioms easy_theorem

/-
## 合同閉包(congruence closure)

`grind` には、合同閉包(congruence closure)アルゴリズムが使用されています。[^lamr]

合同閉包は、等式と不等式のグループが充足可能かどうかを決定するアルゴリズムです。既知の等式から以下のルールによって新たな等式が出てこなくなるまで等式を導出し、矛盾があれば充足不能と判断します。(ただし、無限ループを避けるために合同性ルールの適用は制限します)

* 等式の反射律: `a = a`
* 等式の対称律: `a = b` ならば `b = a`
* 等式の推移律: `a = b` かつ `b = c` ならば `a = c`
* 合同性: `a = b` ならば `f a = f b`
-/
section --#
variable {α : Type} (a₁ a₂ : α)

set_option trace.grind.debug.congr true in

/-⋆-//--
trace: [grind.debug.congr] f a₂ = f a₁
[grind.debug.congr] f (f a₂) = f (f a₁)
-/
#guard_msgs in --#
example (f : α → α) (h : a₁ = a₂) : f (f a₁) = f (f a₂) := by
  grind

-- 複雑な例も扱うことができる
example (f : α → α) (x : α)
  (h1 : f (f (f x)) = x) (h2 : f (f (f (f (f x)))) = x) :
    f x = x := by
  grind

end --#
/- ## E-マッチング

ある定理を適用して新たに分かったことを `grind` が黒板に書き込むことを「定理をインスタンス化する」と呼びます。`grind` は、定理を効率的にインスタンス化するために E-マッチング(E‑matching)と呼ばれる手法を使用します。なおE-マッチングとは、SMT ソルバなどで使われる、等式を考慮したパターンマッチの手法のことです。
-/

/- ### grind_pattern

`grind_pattern` コマンドを使うと、特定の定理をいつインスタンス化するかを `grind` タクティクに指示することができます。

`grind_pattern (定理名) => (パターン)` という構文で使用し、「ローカルコンテキストに宣言されたパターンが見つかった時に定理をインスタンス化してください」という指示をしたことになります。

{{#include ./Grind/IsChain.md}}
-/

/- ### [grind =]

等式を主張する定理に `[grind =]` 属性を付与すると、結論の等式の左辺がパターンとして登録され、「左辺を見かけたらその定理をインスタンス化して、黒板に新たな事実を書き留める」という挙動をするようになります。
-/

def f : Nat → Nat := fun x => x - 1

def g : Nat → Nat := fun x => x + 1

theorem fg (x : Nat) : f (g x) = x := by
  dsimp [f, g]

-- `f (g x)` を見かけたら `f (g x) = x` という事実を
-- 黒板に書き込んで覚えておくよう指示
attribute [grind =] fg

set_option trace.grind.assert true in
set_option trace.grind.debug.congr true in
set_option trace.grind.ematch.instance true in

/-⋆-//--
trace: [grind.assert] f a = b
[grind.assert] a = g c
[grind.assert] ¬b = c
[grind.ematch.instance] fg: f (g c) = c
[grind.assert] f (g c) = c
[grind.debug.congr] f (g c) = f a
-/
#guard_msgs in --#
example (a b c : Nat) (h1 : f a = b) (h2 : a = g c) : b = c := by
  grind

/- なお、結論が等式になっていないような命題に付与するとエラーになります。 -/

theorem bar (n m : Nat) (h : n ≤ m) (hm : m = 1) : n ≤ 1 := by
  grind

/-⋆-//--
error: invalid E-matching equality theorem, conclusion must be an equality
  n ≤ 1
-/
#guard_msgs in --#
attribute [grind =] bar

/- ### [grind \_=\_]

等式を主張する定理に `[grind _=_]` 属性を付与すると、結論の等式の左辺と両辺がともにパターンとして登録され、「左辺か右辺のパターンを見かけたら定理を黒板に書き込む」という挙動をするようになります。
-/

/-- 自前で定義した可換モノイド -/
class CommMonoid (M : Type) [One M] [Mul M] where
  /-- 掛け算は結合的 -/
  mul_assoc : ∀ a b c : M, (a * (b * c)) = ((a * b) * c)
  /-- 単位元を左から掛けても変わらない -/
  one_mul : ∀ a : M, (1 * a) = a
  /-- 単位元を右から掛けても変わらない -/
  mul_one : ∀ a : M, (a * 1) = a
  /-- 掛け算は可換 -/
  mul_comm : ∀ a b : M, (a * b) = (b * a)

namespace CommMonoid

variable {M : Type} [One M] [Mul M] [inst : CommMonoid M]

@[grind _=_]
theorem mul_assoc' (a b c : M) : a * (b * c) = (a * b) * c := by
  apply mul_assoc

@[grind =]
theorem mul_comm' (a b : M) : a * b = b * a := by
  apply mul_comm

example (a b c : M) : a * b * (c * c * a) = a * a * b * c * c := by
  grind

end CommMonoid
/- なお、結論が等式になっていないような定理に付与するとエラーになります。 -/
/-⋆-//--
error: invalid E-matching equality theorem, conclusion must be an equality
  n ≤ 1
-/
#guard_msgs in --#
@[grind _=_]
theorem bar₂ (n m : Nat) (h : n ≤ m) (hm : m = 1) : n ≤ 1 := by
  grind

/- ### [grind →]

定理に `[grind →]` 属性を付与すると、定理の前提の命題が満たされたときに定理がインスタンス化されるようになります。
-/
section --#

/-- 自然数上の広義の順序関係を再定義する -/
protected inductive Nat.myle (n : Nat) : Nat → Prop
  /-- `∀ n, n ≤ n` -/
  | refl : Nat.myle n n
  /-- `n ≤ m`ならば`n ≤ m + 1` -/
  | step {m : Nat} : Nat.myle n m → Nat.myle n (m + 1)

/-- `Nat.myle`のための記号。標準の`≤`と被らないようにする -/
infix:50 " ≤? " => Nat.myle

attribute [grind →] Nat.myle.step

variable {m n a b k : Nat}

/-- 推移律 -/
@[grind →]
theorem Nat.myle_trans (hnm : n ≤? m) (hmk : m ≤? k) : n ≤? k := by
  induction hmk with grind

example (h1 : a ≤? b) (h2 : b ≤? k) (h3 : k ≤? m) : a ≤? m := by
  grind

end --#
/- ### [grind =>]

定理に `[grind =>]` 属性を付与すると、定理の前提が見つかったときに定理がインスタンス化されるようになります。この場合、定理の前提は命題である必要はありません。
-/

/-- 群 -/
class Group (G : Type) extends One G, Mul G, Inv G where
  /-- 単位元を右から掛けても変わらない -/
  mul_one (g : G) : g * 1 = g
  /-- 単位元を左から掛けても変わらない -/
  one_mul (g : G) : 1 * g = g
  /-- 元とその逆元を掛けると単位元になる -/
  mul_inv_cancel (g : G) : g * g⁻¹ = 1
  /-- 逆元と元を掛けると単位元になる -/
  inv_mul_cancel (g : G) : g⁻¹ * g = 1
  /-- 掛け算は結合的である -/
  mul_assoc (g₁ g₂ g₃ : G) : (g₁ * g₂) * g₃ = g₁ * (g₂ * g₃)

attribute [grind =>]
  Group.mul_one Group.one_mul
  Group.mul_inv_cancel Group.inv_mul_cancel Group.mul_assoc

namespace Group

variable {G : Type} [Group G]

@[grind =>]
theorem mul_right_inv {g h : G} (hy : g * h = 1) : h = g⁻¹ := calc
  _ = 1 * h := by grind
  _ = g⁻¹ := by grind

@[grind =>]
theorem mul_left_inv {g h : G} (hy : h * g = 1) : h = g⁻¹ := by
  grind

theorem inv_inv (g : G) : g⁻¹⁻¹ = g := by
  grind

end Group
/- ### [grind intro]

帰納的命題に `[grind intro]` 属性を付与すると、コンストラクタの適用を自動で行うようになります。
-/

/-- 偶数であることを表す帰納的述語 -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | step {n : Nat} : Even n → Even (n + 2)

example : Even 0 := by
  -- 最初は証明できない
  fail_if_success grind

  apply Even.zero

example {m : Nat} (h : Even m) : Even (m + 2) := by
  -- 最初は証明できない
  fail_if_success grind
  apply Even.step h

attribute [grind intro] Even

example : Even 0 := by
  grind

example {m : Nat} (h : Even m) : Even (m + 2) := by
  grind

/- ## ガイド付き場合分け(guided case analysis)

`grind` は `match` 式や `if` 式を場合分けして分解することができます。
-/

def oneOrTwoIf (n : Nat) : Nat :=
  if n = 0 then 1 else 2

example (n : Nat) : oneOrTwoIf n > 0 := by
  dsimp [oneOrTwoIf]
  grind

def oneOrTwoMatch (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | _ => 2

-- どういう場合分けを行ったかトレースを出す
set_option trace.grind.split true in

/-⋆-//--
trace: [grind.split] match n with
    | 0 => 1
    | x => 2, generation: 0
-/
#guard_msgs in --#
example (n : Nat) : oneOrTwoMatch n > 0 := by
  dsimp [oneOrTwoMatch]
  grind

/- `[grind cases]` 属性が付与されている帰納的命題に対しても、場合分けを行います。 -/

example : ¬ Even 1 := by
  -- まだ示せない
  fail_if_success grind

  -- grind なしで証明する
  intro h
  cases h

-- 属性を付与する
attribute [grind cases] Even

example : ¬ Even 1 := by
  -- grind で示せるようになった
  grind

/- ## 制約伝播(Constraint Propagation)

`grind` タクティクが黒板に新たな事実を書き込み、`True` または `False` の同値類が更新されたとき、`grind` は多数の前方推論を行い、新たな事実を導出していきます。これを制約伝播(Constraint Propagation)と呼びます。

制約伝播で使用される導出ルールには様々な種類のものがあります。

### ブール演算

`grind` は `A` が `True` であれば `A ∨ B` も `True` である、などの基本的な導出を行います。
-/

example {P Q : Prop} (h : P) : P ∨ Q := by
  grind

example {P Q R : Prop} (h : P ∧ Q ∧ R) : P ∧ Q := by
  grind

example (a : Bool) : (a && !a) = false := by
  grind

/-
[^reference]: このページの記述は全体的に The Lean Language Reference の [The grind tactic という章](https://lean-lang.org/doc/reference/latest/The--grind--tactic/#grind) と Lean4 リポジトリの [grind_guide ファイル](https://github.com/leanprover/lean4/blob/master/tests/lean/run/grind_guide.lean)を参考にしています。

[^impressive]: この例は Zulip の [Grind is impressive](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Grind.20is.20impressive/with/542704821) というトピックにおける Sorrachai Yingchareonthawornchai さんの投稿を元にしたものです。

[^lamr]: [Marijn J. H. Heule "Logic and Mechanized Reasoning"](https://www.cs.cmu.edu/~mheule/15311-s24/slides/congruence-closure.pdf) を参考にしました。
-/
