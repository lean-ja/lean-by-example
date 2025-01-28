/- # Prop
`Prop` は、命題全体がなす型宇宙です。

命題とは、直観的には「曖昧さなしに真か偽かが定まっているような文章」のことです。たとえば `1 + 1 = 2` は命題です。`1 + 1 = 3` も（偽ではありますが）命題です。
-/

#check (1 + 1 = 2 : Prop)
#check (1 + 1 = 3 : Prop)

/- ## カリー・ハワード同型対応

Lean では、各命題 `P : Prop` は再び型になっています。これは通常の数学では考えないことなので慣れないとわかりにくいのですが、言い換えれば命題 `P` の項というものを考えることができます。

たとえば、`1 + 1 = 2` という命題に対して、その項を構成することができます。
-/

-- `1 + 1 = 2` という型を持つ項を、`rfl` で構成できる
#check (rfl : 1 + 1 = 2)

-- 項に名前を付けた
def one_and_one_eq_two : 1 + 1 = 2 := rfl

/- 実は、いま構成した `1 + 1 = 2` という型の項は `1 + 1 = 2` の証明になっています。実際のところ、命題 `P : Prop` の証明とは、Lean においては項 `h : P` そのものです。このことを強調するために、 **証明項(proof term)** という呼び方をすることもあります。-/

-- さっき構成した証明項で証明ができる
example : 1 + 1 = 2 := one_and_one_eq_two

/- このように命題を型として、証明を項として実装できるのは、そもそも直観主義論理と型付きラムダ計算の間に **カリー・ハワード同型対応(correspondence)** が存在するからです。簡単に言えば、論理と計算（プログラム）は出自は全く異なるものの何故か同じ構造を持っており、同じものであると見なせるということです。-/

/- ## 命題論理
[`Bool`](#{root}/Type/Bool.md) には真と偽に対応する `true` と `false` という項がありますが、`Prop` では真偽は `True` と `False` で表されます。

`P Q : Prop` があるとき、次のようにして新しい命題を得ることができます。

### 論理積 P ∧ Q

論理積 `P ∧ Q` は `P` と `Q` がともに成り立つと主張します。「`P` かつ `Q`」と読みます。`P` と `Q` がともに真であるときに限り真となり、それ以外のときは偽となります。-/

#guard True ∧ True
#guard (True ∧ False) = False
#guard (False ∧ True) = False
#guard (False ∧ False) = False

/- Lean では `And` という名前の[構造体](../Declarative/Structure.md)として表現されます。-/

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := And.intro hP hQ

/- ### 論理和 P ∨ Q

論理和 `P ∨ Q` は `P` または `Q` の少なくとも一つが成り立つという主張です。「`P` または `Q`」と読みます。`P` と `Q` がともに偽であるときに限って偽になり、それ以外のときは真となります。-/

#guard True ∨ True
#guard True ∨ False
#guard False ∨ True
#guard (False ∨ False) = False

/- Lean では `Or` という名前の[帰納型](../Declarative/Inductive.md)として表現されます。-/

example (P Q : Prop) (hP : P) : P ∨ Q := Or.inl hP

/- ### 含意 P → Q

含意 `P → Q` は `P` が成り立つならば `Q` が成り立つという主張です。「`P` ならば `Q`」と読みます。`P` が真であるのに `Q` が偽であるときだけ `P → Q` は偽となり、それ以外のときは `P → Q` は真となります。特に 前提 `P` が偽のときは `P → Q` は `Q` に関わらず真となります。`P` を仮定すれば `Q` が成り立つ、という意味であると解釈しても問題ありません。
-/

#guard (True → True)
#guard (True → False) = False
#guard (False → True)
#guard (False → False)

/- Lean では含意は関数型 `P → Q` として表現されます。これは言い換えれば「`P` の証明項を受け取って `Q` の証明項を返す関数の型」です。含意専用の型を用意せず、関数型を流用することで含意を表現しているのは、Curry Howard 同型対応を利用しているためです。-/

example (P Q : Prop) (hP : P) : Q → P := fun _ => hP

/- ### 否定 ¬ P

否定 `¬ P` は、`P` が成り立たないという主張です。`P` が偽のとき真になり、`P` が真のとき偽になります。-/

#guard (¬ True) = False
#guard (¬ False) = True

/- Lean では `¬ P` は `P → False` として定義されています。-/

example (P : Prop) : (¬ P) = (P → False) := rfl

/- ### 同値 P ↔ Q

同値 `P ↔ Q` は、`P → Q` と `Q → P` がともに成り立つという主張です。読み方は定まっていませんが「`P` と `Q` は同値である」などと読みます。`P` と `Q` の真偽が一致するときに真となり、そうでないとき偽となります。
-/

#guard True ↔ True
#guard (True ↔ False) = False
#guard (False ↔ True) = False
#guard False ↔ False

/- Lean での定義は `P → Q ∧ Q → P` ではありません。`Iff` という専用の構造体が用意されています。 -/

example (P Q : Prop) (hP : P) (hQ : Q) : P ↔ Q :=
  Iff.intro (fun _ => hQ) (fun _ => hP)

/- ## Bool と Prop の違い
どちらも言明に対応するため、`Bool` と似ているようですが以下のような目立つ相違点があります：

1. `Prop` の項はそれ自身が型であるため、`Prop` は型宇宙であると言われます。`Bool` の項は型ではありません。

1. `Prop` の項は `True` か `False` のどちらであるかを判定するアルゴリズムがあるとは限りません。`Bool` の項は簡約すれば必ず `true` か `false` になります。

## 証明無関係 { #ProofIrrel }

`Prop` と同様に `Type` も型宇宙ですが、`Prop` の宇宙としての振る舞いには `Type` との大きな差異が２点あります。それが今から説明する証明無関係と非可述性です。

### 証明にはデータがない

同じ命題 `P : Prop` の２つの証明項 `h1 h2 : P` は必ず等しくなります。直観的には、これは「命題の証明はその命題が真であるという以上の情報を持たない」ということです。これを **証明無関係(proof irrelevance)** と呼びます。
-/

-- 各命題の証明項はただ一つしかない
theorem my_proof_irrel (P : Prop) (h1 h2 : P) : h1 = h2 := rfl

/- 証明無関係は [`axiom`](../Declarative/Axiom.md) で導入された公理から従う定理ではなく、Lean の型システムに組み込まれたものであることに注意してください。-/

/-- info: 'proof_irrel' does not depend on any axioms -/
#guard_msgs in #print axioms proof_irrel

/- ### No Large Elimination { #NoLargeElim }
証明無関係の重要な帰結のひとつに、「証明から値を取り出すことができるのは、証明の中だけ」というものがあります。この現象は、「`Prop` は large elimination を許可しない」という言葉で表現されることがあります。

たとえば次のように、証明の中であれば証明項を [`cases`](../Tactic/Cases.md) や [`rcases`](../Tactic/Rcases.md) で分解して値を取り出すことができます。-/

-- 同じ存在命題の２通りの証明
-- 2乗すると1になる整数を２通り与えた
theorem foo : ∃ x : Int, x ^ 2 = 1 := by exists 1
theorem bar : ∃ x : Int, x ^ 2 = 1 := by exists -1

def Ok.extract (h : ∃ x : Int, x ^ 2 = 1) : True := by
  -- 仮定にある証明項 `h` を分解して
  -- x を取り出すことができる
  rcases h with ⟨_x, _hx⟩

  trivial

/- しかし、命題の証明という文脈ではなく関数の定義という文脈（つまり返り値の型が命題ではない状況）にすると一転、分解することができなくなります。これは証明無関係の制約によるものです。-/

-- 仮定で存在が主張されている `x` を取得して、
-- 返り値として返すために返り値の型を `Int` に変更するとエラーになる
/--
error: tactic 'cases' failed, nested error:
tactic 'induction' failed, recursor 'Exists.casesOn' can only eliminate into Prop
h : ∃ x, x ^ 2 = 1
⊢ Int
-/
#guard_msgs (whitespace := lax) in
  def Bad.extract (h : ∃ x : Int, x ^ 2 = 1) : Int := by
    -- x を取り出すことができない
    obtain ⟨x, hx⟩ := h
    exact x

/- 仮に、上記の例がエラーにならなかったとすると、証明無関係を利用して矛盾を示すことができてしまいます。-/

-- 仮に `x` を何らかの方法で取り出せたとすると、次のような関数が得られるはず
opaque extract (h : ∃ x : Int, x ^ 2 = 1) : Int

-- そして、次のような条件を満たすはずである
axiom extract_foo : extract foo = 1
axiom extract_bar : extract bar = -1

-- このとき、以下のように矛盾が得られる
example : False := by
  -- 証明無関係により `foo` と `bar` は等しい
  have irr : foo = bar := by rfl

  -- extract が満たすべき条件から、`1 = -1` が導けてしまう
  have : 1 = -1 := calc
    1 = extract foo := by rw [extract_foo]
    _ = extract bar := by rw [irr]
    _ = -1 := by rw [extract_bar]

  -- これは矛盾
  contradiction

/- ## 非可述性 { #Impredicativity }
もう一つの重要な `Prop` と `Type` の差異が **非可述性(impredicativity)** です。非可述性について簡単に概略を述べるのは難しいので、まず例から入りましょう。

型 `α : Type` 上の述語 `P : α → Prop` があるとき、`α` で量化された `∀ x : α, P x` は再び命題になります。
-/
section --#
-- 何かの型
variable (α : Type)

-- α 上の述語
variable (P : α → Prop)

-- 量化しても再び命題になる
#check (∀ (x : α), P x : Prop)

/- 更に一般的に、`α` 上の述語 `α → Prop` に対して量化しても、再び命題になります。-/

variable (x : α)

-- 任意の命題 P に対して P x が成り立つ、という命題
#check (∀ P : α → Prop, P x)
end --#
/-
上記の挙動は `Prop` が命題の型であるという直観的解釈と合致しており、自然な挙動だと感じられると思います。しかしながら、「任意の述語 `P` に対して」と量化して命題を定義することが許されるということは、自分自身に言及するような述語も作ることができるということになります。たとえば、以下の例を考えてみましょう。-/

-- α を型とする
opaque α : Type

/-- α 上の述語 P に対して、それが簡単なものかそうでないか判定する述語 -/
opaque simple (P : α → Prop) : Prop

/-- `x : α` は「簡単な述語を成り立たせることがない」という述語。
このとき項 `x : α` は「難解である」と呼ぶことにする。 -/
def anti_simple (x : α) : Prop :=
  ∀ P : α → Prop, simple P → ¬ P x

/- ここで定義した `anti_simple` という述語は、`α` 上の述語全体に対する量化を含んでいますが、自分自身が `α` 上の述語であるため、自分自身に言及していることになります。いわば定義が循環しています。一般に定義されているものそれ自身が含まれるような定義のことを、**非可述的(impredicative)** であると呼ぶのですが、これはまさに非可述的な定義になっています。

`anti_simple` について、まさに `anti_simple` が自分自身に言及しているということを用いた証明の例を以下に示しておきましょう。
-/

-- 難解な項が存在するならば、`anti_simple` 自身は簡単ではない
example (ex : ∃ x, anti_simple x) : ¬ simple anti_simple := by
  -- 難解な項 x を取り出す
  obtain ⟨x, ex⟩ := ex

  -- anti_simple が簡単だと仮定する
  intro (h : simple anti_simple)

  -- anti_simple 自身が α 上の述語であることから、
  -- anti_simple 自身が簡単ではないことがわかる
  have := ex anti_simple h

  -- これは矛盾
  contradiction

/- 以上が非可述性についての直観的な説明です。より形式的には、型宇宙 `U` に対して、`U` が非可述的であるとは `∀ a : U, a` の型が `U` 自身になることをいいます。 -/

-- 命題の宇宙 Prop は非可述的
#check (∀ a : Prop, a : Prop)

-- 型宇宙 Type は非可述的ではなく、可述的
#check (∀ a : Type, a : Type 1)
