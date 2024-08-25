/- # axiom
`axiom` は、公理(axiom)を宣言するためのコマンドです。公理とは、議論の前提のことで、証明を与えることなく正しいと仮定される命題です。
-/
namespace Axiom --#

/-- sorryAx を真似て作った公理 -/
axiom mySorryAx {P : Prop} : P

-- 任意の命題を示すことができる
theorem FLT : ∀ x y z n : Nat, n > 2 → x^n + y^n ≠ z^n := by
  apply mySorryAx

/-- info: 'Axiom.FLT' depends on axioms: [Axiom.mySorryAx] -/
#guard_msgs in #print axioms FLT

/- ## 組み込みの公理
組み込みで用意されている公理をいくつか紹介します。

### 命題外延性 propext
命題外延性の公理 `propext` は、同値な命題は等しいという公理です。この公理があることにより、どのような状況でも常に命題をそれと同値な命題と置き換えることができます。
-/

-- 命題外延性の公理
/-- info: axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b -/
#guard_msgs in #print propext

-- 命題外延性の公理を使って命題を置換する
theorem ex_prop_ext (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b := by
  have := propext h
  rw [←this]
  assumption

/-- info: 'Axiom.ex_prop_ext' depends on axioms: [propext] -/
#guard_msgs in #print axioms ex_prop_ext

/- ### 商の公理 Quot.sound
任意の型 `α : Sort u` と `α` 上の2項関係 `r : α → α → Prop` に対して、その商(quotient)を作ることができます。商の概念は、以下に示す複数の定数から構成されます。
-/
section quot --#
universe u

variable {α : Sort u}

-- 商
#check (Quot : (α → α → Prop) → Sort u)

-- 商の構築
#check (Quot.mk : (r : α → α → Prop) → α → Quot r)

-- 帰納法の原理。
-- 任意の部分集合 `β ⊆ Quot r` に対して、
-- β が `Quot.mk r a` の形の項を全て含むならば、
-- β は商 `Quot r` 全体に一致する。
#check (Quot.ind :
  {r : α → α → Prop} → {β : Quot r → Prop}
  → (∀ a, β (Quot.mk r a)) → ∀ q, β q)

-- 要するに商 `Quot r` の全ての項は `Quot.mk r a` の形をしている。
-- Quot.ind から直ちに従う。
example (r : α → α → Prop) (q : Quot r) : ∃ a : α, q = Quot.mk r a := by
  have := Quot.ind (β := fun q => ∃ a : α, q = Quot.mk r a)
  apply this
  intro a
  exists a

-- 関数の商へのリフト。
-- 関数 `f : α → β` が、関係 `r` に関して合同性を持つならば、
-- `f` をリフトして関数 `Quot r → β` が得られる。
#check (Quot.lift :
  {r : α → α → Prop} → {β : Sort u} → (f : α → β)
  → (∀ a b, r a b → f a = f b) → Quot r → β)

/- 商の公理 `Quot.sound` は上記の「商のような」概念を本物の商にします。-/

-- `r a b` が成り立つならば、商に送った時に同じ値になることを主張する。
/--
info: axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
r a b → Quot.mk r a = Quot.mk r b
-/
#guard_msgs in #print Quot.sound

/- #### 商の公理はなぜ重要か
上記で挙げた商を構成する定数

* 型 `Quot`
* コンストラクタ `Quoto.mk`
* 帰納法の原理 `Quot.ind`
* 関数の商へのリフト `Quot.lift`
* 商の公理 `Quot.sound`

はいずれも他の型からは独立したオブジェクトですが、`Quot.sound` だけが「公理」と呼ばれ、特別扱いされているのは何故でしょうか。以下のように商の公理以外の部分を Lean の帰納型を使って構成してみると理解できるかもしれません。
-/

/-- 標準ライブラリの Quot を真似して自作した型 -/
inductive MyQuot (r : α → α → Prop) : Type u where
  | mk (a : α) : MyQuot r

-- 商型のコンストラクタ
#check (MyQuot.mk : {r : α → α → Prop} → α → MyQuot r)

-- 自動生成された商型の帰納法の原理
-- Quot.ind とそっくりであることがわかる
#check (MyQuot.rec :
  {r : α → α → Prop} → {β : MyQuot r → Sort _}
  → (mk : ∀ a : α, β (MyQuot.mk a)) → ∀ q, β q)

/- ここで、関数の商へのリフト `Quot.lift` に対応するものを具体的に関数として作ることができます。-/

/-- 商へのリフトの対応物 -/
def MyQuot.lift {r : α → α → Prop} {β : Sort u}
  (f : α → β) (_ : ∀ a b, r a b → f a = f b) : MyQuot r → β
  | MyQuot.mk a => f a

end quot --#
/- こうして `Quot.sound` を使わず、Lean に備わっている帰納型の構成だけを使って作った `MyQuot` は、商の公理以外のすべての点で商型にそっくりですが、全然商になっていません。コンストラクタを使って作られる項 `MyQuot.mk a` は、`a : α` が異なればすべて異なる項であり、同一視が全く入っていません。このような観点から、`Quot.sound` は商を商たらしめる重要なものであり、「商の公理」と呼ぶにふさわしいと考えられるわけです。 -/

/- #### 関数外延性
商の公理 `Quot.sound` を利用して、関数外延性を示すことができます。関数外延性とは、関数 `f, g` について `∀ x, f x = g x` という仮定から `f = g` が示せるという定理です。直観的には「すべての入力に対して同じ値を返すような２つの関数は等しい」と主張しています。

実際に証明していきます。一般に証明を理解するためには、前提を確認することが大切です。「商の公理を使用しなくても、前提として等しいことが分かっているものは何か」をまず確認しましょう。前提として利用できる事実には、次の２つがあります：

* 関数 `f` とラムダ式 `fun x => f x` は等しい。（これは **η 簡約(eta reduce)** と呼ばれます）
* 関数 `f` と、「関数 `f` を適用する関数」は等しい。

実際に、公理を一切使わずにこれは証明できます。
-/

universe u v

variable {α : Type u} {β : α → Sort v}

/-- η 簡約。依存関数はラムダ式と等しい。 -/
theorem lambda_eq (f : (x : α) → β x) : f = (fun x => f x) := by rfl

-- 依存関数 `f` がラムダ式 `fun x => f x` に等しいことは、定義から従うので
-- 何の公理も必要としない。
/-- info: 'Axiom.lambda_eq' does not depend on any axioms -/
#guard_msgs in
  #print axioms lambda_eq

/-- 関数適用を行う高階関数 -/
def funApp (a : α) (f : (x : α) → β x) : β a := f a

/-- 「`f` を適用する関数」と `f` は等しい -/
theorem funApp_eq (f : (x : α) → β x) : funApp (f := f) = f := calc
  -- 関数とラムダ式は等しい
  funApp (f := f) = (fun a => funApp a f) := by rw [lambda_eq funApp]

  -- funApp の定義から等しい
  _ = (fun a => f a) := by dsimp only [funApp]

  -- 関数とラムダ式は等しい
  _ = f := by rw [lambda_eq f]

-- これも何の公理も必要としない
/-- info: 'Axiom.funApp_eq' does not depend on any axioms -/
#guard_msgs in
  #print axioms funApp_eq

/- この事実を使うと、商の公理から関数外延性の証明ができます。-/

/-- 関数外延性の定理 -/
theorem my_funext {f g : (x : α) → β x} (h : ∀ x, f x = g x) : f = g := by
  -- 外延性等式を表す二項関係を定義する
  let eqv (f g : (x : α) → β x) := ∀ x, f x = g x

  -- 二項関係 eqv で `(x : α) → β x` の商を取る
  let «[(x : α) → β x]» := Quot eqv

  -- 関数 `f` と `g` は商の公理から、商に送ると等しいことに注意する。
  -- 商の公理はここで使っている。
  have : Quot.mk eqv f = Quot.mk eqv g := Quot.sound (λ x => h x)

  -- 関数適用 `funApp` は、適用する項 `a` を固定すれば `(x : α) → β x` 上の関数と見なせる。
  -- この関数は同値関係 `eqv` を保つため、
  -- 関数適用 `funApp` を商 `«[(x : α) → β x]»` 上に持ち上げることができる。
  let «[funApp]» (a : α) (f' : «[(x : α) → β x]») : β a := by
    have lift := @Quot.lift ((x : α) → β x) eqv (β a) (funApp a)
    apply lift
    · intro f g h
      exact h a
    · exact f'

  -- `f = g` を示す問題を `«[funApp]»` をかませることで、
  -- 商での等式に帰着させることができる。
  exact show f = g from calc
    -- 「`f` を適用する関数」と `f` は等しい
    f = funApp (f := f) := by rw [funApp_eq f]

    -- 商への関数の持ち上げの定義から等しい
    _ = «[funApp]» (f' := Quot.mk eqv f) := by rfl

    -- 関数 `f` と `g` は商の公理から、商に送ると等しい
    _ = «[funApp]» (f' := Quot.mk eqv g) := by rw [this]

    -- 商への関数の持ち上げの定義から等しい
    _ = funApp (f := g) := by rfl

    -- 「`g` を適用する関数」と `g` は等しい
    _ = g := by rw [funApp_eq g]

/-- info: 'Axiom.my_funext' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms my_funext

/- ### 選択原理 Classical.choice { #ClassicalChoice }
選択原理は、ある型が空ではないという情報だけから、「魔法のように」具体的な元を構成することができると主張します。これは計算不可能な操作であるため、選択原理を使用する関数には [`noncomputable`](./Noncomputable.md) 修飾子が必要になります。

選択原理は数学でいうと NBG(Neumann-Bernays-Gödel) 集合論における大域選択公理(axiom of global choice)とよく似ています。
-/

-- 選択原理は、空でない型から具体的な元を構成する
#check (Classical.choice : {α : Sort u} → Nonempty α → α)

/-
ここで、ある型が空ではないという主張は `Nonempty` という型クラスで表現されています。`Nonempty α` は `∃ e : α, True` と同値なので、存在命題だと思って構いません。-/
set_option linter.unusedVariables false in --#

example (α : Type) : Nonempty α ↔ ∃ e : α, True := by
  constructor
  · intro ⟨a⟩
    exists a
  · intro ⟨a, _⟩
    exact ⟨a⟩

/- #### 存在命題に対する選択

選択原理は単に項を取ってくる関数ですが、選んだ項が満たすべき性質が欲しいこともあります。言い換えれば、存在命題 `∃ x : α, P x` が成り立っているとき、`P x` が成り立つような `x : α` を取ってくる関数が必要なこともあります。それは選択原理を使って次のように構成することができます。
-/

variable {α : Sort u}

noncomputable def indefiniteDescription (p : α → Prop) (h : ∃ x, p x) : {x // p x} := by
  -- 選択原理を使用する
  apply Classical.choice

  -- p x となる x が存在することを示せばよい
  show Nonempty {x // p x}

  -- 仮定の存在命題から x を取り出す
  obtain ⟨x, px⟩ := h

  -- この x が所望の条件を満たす
  exact ⟨x, px⟩

/- Lean のライブラリ上では、存在命題から選択する関数には `Classical.choose` という名前が、選択された項が満たすべき性質には `Classical.choose_spec` という名前がついています。 -/

variable {p : α → Prop}

-- 存在命題から選択する関数
#check (Classical.choose : (h : ∃ x, p x) → α)

-- 選択された要素が満たす性質
#check (Classical.choose_spec : (h : ∃ x, p x) → p (Classical.choose h))

/- #### なぜ証明無関係と矛盾しないのか
[証明無関係](../../Term/Type/Prop.md#ProofIrrel)の節で詳しく述べているように、存在命題は「何かがある」としか主張しておらず、具体的な項を復元するのに必要な情報を持っていません。したがって存在が主張されている項を取り出して関数の返り値にすることはできないはずですが、選択原理を使うと存在命題から具体的な項が得られてしまいます。これが矛盾を生まないのはなぜでしょうか？

答えは、選択原理は証明方法が異なる証明項であっても、同じ命題であれば一様に同じ項を返すからです。以下の例では、「証拠」が異なるような存在命題の証明項を２つ与えていますが、そこから選択される項は同じです。つまり、選択原理は同値な存在命題すべてに対して一斉に同じ項を取り出す方法があると主張しているのであって、「存在が主張されている項を取り出して関数の返り値にする」ことができるとまでは主張していないのです。-/

-- 同じ存在命題の２通りの証明
-- 2乗すると1になる整数を２通り与えた
theorem foo : ∃ x : Int, x ^ 2 = 1 := by exists 1
theorem bar : ∃ x : Int, x ^ 2 = 1 := by exists -1

open Classical in

-- 選択される項は同じ
example : choose foo = choose bar := by rfl

/- #### 排中律
選択原理と命題外延性と関数外延性を併せると、排中律を証明することができます。これは [Diaconescuの定理](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem) として知られる結果です。以下にその証明を示しましょう。

まず、命題論理から始めます。排中律は任意の命題 `P : Prop` に対して `P ∨ ¬ P` が成り立つという主張ですが、これを示すにはある命題 `Q : Prop` に対して「`P → Q` かつ `¬ Q ∨ P`」を示せば十分です。
-/

variable (P Q : Prop)

/-- 排中律を証明するための主要な補題 -/
theorem lemma_em (himp : P → Q) (hor : ¬ Q ∨ P) : P ∨ ¬ P := by
  rcases hor with h | h
  · right
    intro hP
    have := himp hP
    contradiction
  · left
    exact h

-- 何の公理も使用していない
/-- info: 'Axiom.lemma_em' does not depend on any axioms -/
#guard_msgs in #print axioms lemma_em

/- 選択原理を用いると命題 `Q` を構成することができ、関数外延性と命題外延性により、それが所望の性質を持つことを示すことができます。-/

/-- 排中律 -/
theorem em (P : Prop) : P ∨ ¬ P := by
  -- Prop の部分集合 U と V を考える
  let U (x : Prop) : Prop := (x = True) ∨ P
  let V (x : Prop) : Prop := (x = False) ∨ P

  -- U と V は空ではない
  have exU : ∃ x, U x := ⟨True, by simp [U]⟩
  have exV : ∃ x, V x := ⟨False, by simp [V]⟩

  -- したがって、選択原理を使って `u ∈ U` と `v ∈ V` を選ぶことができる
  let u : Prop := Classical.choose exU
  let v : Prop := Classical.choose exV
  have u_def : U u := Classical.choose_spec exU
  have v_def : V v := Classical.choose_spec exV

  -- 選択原理を使用したご利益として、u と v は一貫した方法で選択されているので、
  -- `U = V` ならば `u = v` が成り立つ。
  -- これは `u = True`, `v = False` などと構成した場合は示せないことに注意。
  have eq_of_eq (h : U = V) : u = v := by
    simp [u, v, h]

  -- `Q := u = v` として `Q` を構成する
  apply lemma_em (Q := u = v)

  case himp =>
    show P → u = v

    -- P が成り立つと仮定する
    intro (hP : P)

    -- `U = V` を示せばよい
    apply eq_of_eq

    -- U と V の定義を展開する
    dsimp [U, V]

    -- 関数外延性によってゴールを書き換える
    ext x

    -- あとは命題論理の問題になる
    -- 仮定に P があるので自明
    show x = True ∨ P ↔ x = False ∨ P
    simp [hP]

  case hor =>
    show (u ≠ v) ∨ P

    -- U と V の定義を展開する
    replace u_def : u ∨ P := by simpa [U] using u_def
    replace v_def : ¬ v ∨ P := by simpa [V] using v_def

    -- これにより４通りの場合分けが生じるが、１つを除いてすべて P が成り立つ。
    rcases u_def with hu | hu <;> rcases v_def with hv | hv
    all_goals (try right; assumption)

    -- 残りの１つでは `u ≠ v` が成り立つ。
    simp [hu, hv]

end Axiom --#
