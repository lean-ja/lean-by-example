/- # grind

`grind` は、現代の SMT ソルバにインスパイアされた証明自動化タクティクです。[^reference]

非常に強力であり、時に驚くほどギャップのある証明を自動で完了させることができます。[^impressive]
-/

/-- 階乗関数 -/
@[grind] def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

@[inherit_doc factorial]
notation:max n "!" => factorial n

/-- 階乗関数の値は１以上 -/
theorem one_le_factorial (n : Nat) : 1 ≤ n ! := by
  fun_induction factorial <;> grind

-- `n !` を見かけたら `one_le_factorial` をインスタンス化して利用するよう指示
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

/-
## 合同閉包(congruence closure)

`grind` の中核には、合同閉包(congruence closure)アルゴリズムが使用されています。これは、黒板に「今まで分かったこと」を蓄積していくところをイメージすると分かりやすいかもしれません。

`grind` は新しい等式や不等式を発見するたびに、その事実を黒板に書き込んでいきます。そして、「互いに等しいと分かっているグループ」を同値類(equivalence class)としてまとめて管理します。この同値類を「バケツ」と呼ぶことがあります。

`grind` は合同性(congruence)つまり `a₁ = a₂` ならば `f a₁ = f a₂` が成り立つことを認識しているので、そういったパターンを見つけると黒板に書き込んでいきます。
-/
section --#
variable {α : Type} (a₁ a₂ : α)

set_option trace.grind.debug.congr true

/-⋆-//--
trace: [grind.debug.congr] f a₂ = f a₁
[grind.debug.congr] f (f a₂) = f (f a₁)
-/
#guard_msgs in --#
example (f : α → α) (h : a₁ = a₂) : f (f a₁) = f (f a₂) := by
  grind

end --#
/- なお、`grind` は初手で結論の否定を黒板に書き込み、矛盾を示す（つまり `True` の同値類と `False` の同値類をマージする）ことでゴールを閉じるという設計になっていることに注意してください。特に、`grind` はそれが不要な場合であっても選択原理を使用することがあります。 -/

set_option trace.grind.assert true in
set_option trace.grind.eqc true in

/-⋆-//--
trace: [grind.assert] P
[grind.eqc] P = True
[grind.assert] ¬P
[grind.eqc] P = False
-/
#guard_msgs in --#
theorem foo (P : Prop) (h : P) : P := by
  grind

/-⋆-//-- info: 'foo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in --#
#print axioms foo

/- ## E-マッチング

新たに分かったことを `grind` が黒板に書き込むことを「定理をインスタンス化する」と呼びます。`grind` は、定理を効率的にインスタンス化するために E-マッチング(E‑matching)と呼ばれる手法を使用します。なおE-マッチングとは、SMT ソルバなどで使われる、等式を考慮したパターンマッチの手法のことです。

### [grind =]

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

等式を主張する定理に `[grind _=_]` 属性を付与すると、結論の等式の左辺と両辺がともにパターンとして登録され、「左辺か右辺のパターンを見かけたら定理をホワイトボードに書き込む」という挙動をするようになります。
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

/-- 標準の`≤`を`myle`で置き換える -/
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
class Group (G : Type) [One G] [Mul G] [Inv G] where
  /-- 単位元を右から掛けても変わらない -/
  mul_one : ∀ g : G, g * 1 = g
  /-- 単位元を左から掛けても変わらない -/
  one_mul : ∀ g : G, 1 * g = g
  /-- 元とその逆元を掛けると単位元になる -/
  mul_inv : ∀ g : G, g * g⁻¹ = 1
  /-- 逆元と元を掛けると単位元になる -/
  inv_mul : ∀ g : G, g⁻¹ * g = 1
  /-- 掛け算は結合的である -/
  mul_assoc : ∀ g₁ g₂ g₃ : G, g₁ * (g₂ * g₃) = (g₁ * g₂) * g₃

namespace Group

variable {G : Type} [One G] [Mul G] [Inv G] [Group G]

attribute [grind =>]
  Group.mul_one Group.one_mul
  Group.mul_inv Group.inv_mul Group.mul_assoc

theorem mul_right_inv {g h : G} (hy : g * h = 1) : h = g⁻¹ := calc
  _ = 1 * h := by grind
  _ = g⁻¹ := by grind

@[grind =>]
theorem mul_left_inv {g h : G} (hy : h * g = 1) : h = g⁻¹ := calc
  _ = h * 1 := by grind
  _ = g⁻¹ := by grind

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

/- ## ケース分割

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

-- どういうケース分割を行ったかトレースを出す
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

/- `[grind cases]` 属性が付与されている帰納的命題に対しても、ケース分割を行います。 -/

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

`grind` タクティクがホワイトボードに新たな事実を書き込み、`True` または `False` の同値類が更新されたとき、`grind` は多数の前方推論を行い、新たな事実を導出していきます。これを制約伝播(Constraint Propagation)と呼びます。

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
[^reference]: このページの記述は全体的に The Lean Language Reference の [The grind tactic という章](https://lean-lang.org/doc/reference/latest/The--grind--tactic/#grind) と Lean4 リポジトリの [grind_guide ファイル](https://github.com/leanprover/lean4/blob/4322a0c7d33fd6722caf84b2c780d72cf824993e/tests/lean/run/grind_guide.lean)を参考にしています。

[^impressive]: この例は Zulip の [Grind is impressive](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Grind.20is.20impressive/with/542704821) というトピックにおける Sorrachai Yingchareonthawornchai さんの投稿を元にしたものです。
-/
