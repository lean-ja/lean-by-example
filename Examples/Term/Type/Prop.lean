/- # Prop
`Prop` は、命題全体がなす型宇宙です。

どちらも言明に対応するため、`Bool` と似ているようですが以下のような目立つ相違点があります：

1. `Prop` の項はそれ自身が型であるため、`Prop` は型宇宙であると言われます。`Bool` の項は型ではありません。

1. `Prop` の項は `True` か `False` のどちらであるかを判定するアルゴリズムがあるとは限りません。`Bool` の項は簡約すれば必ず `true` か `false` になります。

`Prop` と同様に `Type` も型宇宙ですが、`Prop` の宇宙としての振る舞いには `Type` との大きな差異が２点あります。それが今から説明する証明無関係と非可述性です。

## 証明無関係 { #ProofIrrel }

### 証明にはデータがない

同じ命題 `P : Prop` の２つの証明項 `h1 h2 : P` は必ず等しくなります。直観的には、これは「命題の証明はその命題が真であるという以上の情報を持たない」ということです。これを **証明無関係(proof irrelevance)** と呼びます。
-/

namespace Proposition --#

-- 各命題の証明項はただ一つしかない
theorem proof_irrel (P : Prop) (h1 h2 : P) : h1 = h2 := rfl

/- 証明無関係は [`axiom`](../../Command/Declarative/Axiom.md) で導入された公理から従う定理ではなく、Lean の型システムに組み込まれたものであることに注意してください。-/

/-- info: 'Proposition.proof_irrel' does not depend on any axioms -/
#guard_msgs in #print axioms proof_irrel

/- ### No Large Elimination
証明無関係の重要な帰結のひとつに、「証明から値を取り出すことができるのは、証明の中だけ」というものがあります。この現象は、「`Prop` は large elimination を許可しない」という言葉で表現されることがあります。

たとえば次のように、証明の中であれば証明項を [`cases`](../../Tactic/Cases.md) や [`rcases`](../../Tactic/Rcases.md) で分解して値を取り出すことができます。-/

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
  -- 証明無関連により `foo` と `bar` は等しい
  have irr : foo = bar := by rfl

  -- extract が満たすべき条件から、`1 = -1` が導けてしまう
  have : 1 = -1 := calc
    1 = extract foo := by rw [extract_foo]
    _ = extract bar := by rw [irr]
    _ = -1 := by rw [extract_bar]

  -- これは矛盾
  contradiction

/- ## 非可述性
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

/- 以上が非可述性についての直観的な説明です。より形式的には、型宇宙 `U` に対して、`U` が非可述的であるとは `∀ a : U, a → a` の型が `U` 自身になることをいいます。 -/

-- 命題の宇宙 Prop は非可述的
#check (∀ a : Prop, a → a : Prop)

-- 型宇宙 Type は非可述的ではなく、可述的
#check (∀ a : Type, a → a : Type 1)

end Proposition --#
