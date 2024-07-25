/- # Prop
`Prop` は、命題全体がなす型です。

## 証明無関係 { #ProofIrrel }

同じ命題 `P : Prop` の２つの証明項 `h1 h2 : P` は必ず等しくなります。直観的には、これは「命題の証明はその命題が真であるという以上の情報を持たない」ということです。これを **証明無関係(proof irrelevance)** と呼びます。
-/
namespace Proposition --#

-- 各命題の証明項はただ一つしかない
theorem proof_irrel (P : Prop) (h1 h2 : P) : h1 = h2 := rfl

/- 証明無関係は [`axiom`](../../Command/Declarative/Axiom.md) で導入された公理から従う定理ではなく、Lean の型システムに組み込まれたものであることに注意してください。-/

/-- info: 'Proposition.proof_irrel' does not depend on any axioms -/
#guard_msgs in #print axioms proof_irrel

/- 証明無関係の重要な帰結のひとつに、「命題から値を取り出すことができるのは、証明の中だけ」というものがあります。たとえば次のように、証明の中であれば命題を [`cases`](../../Tactic/Cases.md) や `rcases` で分解して値を取り出すことができます。-/

-- 同じ存在命題の２通りの証明
-- 2乗すると1になる整数を２通り与えた
theorem foo : ∃ x : Int, x ^ 2 = 1 := by exists 1
theorem bar : ∃ x : Int, x ^ 2 = 1 := by exists -1

def Ok.extract (h : ∃ x : Int, x ^ 2 = 1) : True := by
  -- 仮定にある存在命題 `h` を分解して
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

end Proposition --#
