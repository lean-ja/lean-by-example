/- # grind

`grind` は、現代の SMT ソルバにインスパイアされた証明自動化タクティクです。[^reference]

## grind の動作原理

### 合同閉包(congruence closure)

`grind` の中核には、合同閉包(congruence closure)アルゴリズムが使用されています。これは、黒板に「今まで分かったこと」を蓄積していくところをイメージすると分かりやすいかもしれません。

`grind` は新しい等式や不等式を発見するたびに、その事実を黒板に書き込んでいきます。そして、「互いに等しいと分かっているグループ」を同値類(equivalence class)としてまとめて管理します。

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

/- ### E-マッチング

新たに分かったことを `grind` が黒板に書き込むことを「定理をインスタンス化する」と呼びます。`grind` は、定理を効率的にインスタンス化するために E-マッチング(E‑matching)と呼ばれる手法を使用します。なおE-マッチングとは、SMT ソルバなどで使われる、等式を考慮したパターンマッチの手法のことです。

#### [grind =]

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

/- #### [grind →]

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
/- #### [grind =>]

等式を主張する定理に `[grind =>]` 属性を付与すると、定理の前提が見つかったときに定理がインスタンス化されるようになります。この場合、定理の前提は命題である必要はありません。
-/
section --#

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

variable {G : Type} [One G] [Mul G] [Inv G] [Group G]

attribute [grind =>]
  Group.mul_one Group.one_mul
  Group.mul_inv Group.inv_mul Group.mul_assoc

theorem mul_right_inv {g h : G} (hy : g * h = 1) : h = g⁻¹ := calc
  _ = 1 * h := by grind
  _ = g⁻¹ := by grind

theorem mul_left_inv {g h : G} (hy : h * g = 1) : h = g⁻¹ := calc
  _ = h * 1 := by grind
  _ = g⁻¹ := by grind

theorem inv_inv (g : G) : g⁻¹⁻¹ = g := by
  grind [mul_right_inv]

end --#
/- ### ケース分割

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

inductive Even : Nat → Prop where
  | zero : Even 0
  | succ : ∀ n, Even n → Even (n + 2)

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

/-
[^reference]: このページの記述は全体的に The Lean Language Reference の [The grind tactic という章](https://lean-lang.org/doc/reference/latest/The--grind--tactic/#grind) と Lean4 リポジトリの [grind_guide ファイル](https://github.com/leanprover/lean4/blob/4322a0c7d33fd6722caf84b2c780d72cf824993e/tests/lean/run/grind_guide.lean)を参考にしています。
-/
