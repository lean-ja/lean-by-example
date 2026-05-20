/- # partial_fixpoint

`partial_fixpoint` は、[`partial`](#{root}/Modifier/Partial.md) と同様に「すべての入力に対して必ずしも停止しないような関数」を定義することを可能にしますが、`partial` とは異なり定義した関数を証明に使うことが可能です。
-/

variable {α : Type}

/-- `partial` で定義された検索関数 -/
partial def searchP (f : Nat → Option α) (start : Nat) : Option Nat :=
  match f start with
  | some _ => some start
  | none => searchP f (start + 1)

/-- `partial_fixpoint` で定義された検索関数 -/
@[grind]
def searchF (f : Nat → Option α) (start : Nat) : Option Nat :=
  match f start with
  | some _ => some start
  | none => searchF f (start + 1)
partial_fixpoint

set_option warn.sorry false --#

-- `partial` で定義した関数は証明に使うことができない
example (f : Nat → Option α) (n : Nat) (h : (f n).isSome) : (searchP f n).isSome := by
  induction n with
  | zero =>
    -- 全く展開することができず、上手くいかない
    fail_if_success unfold searchP
    sorry
  | succ n ih =>
    sorry

-- `searchF` に関しては証明ができる
example (f : Nat → Option α) (n : Nat) (h : (f n).isSome) : (searchF f n).isSome := by
  induction n with
  | zero =>
    unfold searchF
    grind
  | succ n ih => grind

/-
## なぜ `partial_fixpoint` では健全性が壊れないのか？

`partial_fixpoint` の要点は「停止しない可能性」を **定義上の簡約** ではなく **命題としての展開定理** で扱うところにあります。[^partial-fixpoint-ref]

実際、`searchF` の本体は `rfl` では展開できず、`searchF.eq_def` という補題を使ってはじめて展開できます。
-/

example (f : Nat → Option α) (n : Nat) :
    searchF f n = (match f n with
      | some _ => some n
      | none => searchF f (n + 1)) := by
  fail_if_success exact rfl
  rw [searchF.eq_def]

/-
そのため「`P` は `P` だから真」のような循環を定義上の簡約で作ることはできません。`partial_fixpoint` で得られるのは `Option` などのモナド上での部分正当性に限られます。たとえば次の関数は `n ≠ 0` のとき停止しない可能性がありますが、`False` を直接取り出すことはできません。
-/

@[grind] def divergeOrNone (n : Nat) : Option False :=
  if n = 0 then
    none
  else
    divergeOrNone (n + 1)
partial_fixpoint

example : divergeOrNone 0 = none := by
  rw [divergeOrNone.eq_def]
  simp

example (n : Nat) : (∃ p : False, divergeOrNone n = some p) → False := by
  intro h
  rcases h with ⟨p, _⟩
  exact False.elim p

/-
## 名前の由来

`partial_fixpoint` という名前を見て、`partial` の部分は納得がいくと思います。部分関数(partial function)を定義するための修飾子だからです。では `fixpoint` の部分は何でしょうか？

これを説明するためには、再帰関数について考える必要があります。たとえば、階乗関数を考えてみましょう。
-/

/-- 階乗関数 -/
def Nat.factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-
「引数として `n + 1` を渡すと、自分自身を再帰的に呼びだす」という構造を持っています。`#print equations` コマンドを使うと、ここで定義された関数がどのような関数等式を満たしているかを確認することができます。
-/

/-⋆-//--
info: equations:
@[defeq] theorem Nat.factorial.eq_1 : Nat.factorial 0 = 1
@[defeq] theorem Nat.factorial.eq_2 : ∀ (n_2 : Nat), n_2.succ.factorial = (n_2 + 1) * n_2.factorial
-/
#guard_msgs in --#
#print equations Nat.factorial

/-
「重要なのはこの関数等式であって、定義の仕方自体は表面的なものである」という視点に立つことができます。`Nat.factorial` とは、上記の関数等式を満たす何者かであればよいということです。そう考えると、関数等式さえ表現できるのであれば別の定義の仕方がありえることになります。

そこで、たとえば次のような高階関数を考えてみます。
-/

def factBody (f : Nat → Nat) : Nat → Nat :=
  fun n =>
    match n with
    | 0 => 1
    | n + 1 => (n + 1) * f n

/-
このようにすると、`Nat.factorial` が満たしていた関数等式 `f 0 = 1 ∧ f (n + 1) = (n + 1) * f n` は、`f = factBody f` という等式に置き換えることができます。
-/

example (f : Nat → Nat) (h : f = factBody f) : f 0 = 1 := calc
  _ = factBody f 0 := by rw [h]; grind
  _ = 1 := rfl

example (f : Nat → Nat) (h : f = factBody f)
    : ∀ n : Nat, f (n + 1) = (n + 1) * f n := by
  intro n
  calc
    _ = factBody f (n + 1) := by rw [h]; grind
    _ = (n + 1) * f n := rfl

/-
つまり、階乗関数を「`f = factBody f` を満たす `f`」として定義することができるというわけです。

ここで `f = factBody f` という等式をよく見ると、`f` が `factBody` という高階関数の不動点(fixpoint)であると主張していることがわかります。ここでは階乗関数を具体例にしましたが、一般に再帰関数は関数の不動点として捉えられることが知られています。`partial_fixpoint` の名前は、まさにこの「再帰関数は不動点である」という考え方に由来します。

[^partial-fixpoint-ref]: Lean 公式リファレンス「Recursive functions as partial fixpoints」「Partial functions with nonempty codomains」を参照：<https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#partial-fixpoint>
-/
