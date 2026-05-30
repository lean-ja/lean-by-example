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

/--
info: equations:
@[backward_defeq] theorem Nat.factorial.eq_1 : Nat.factorial 0 = 1
@[backward_defeq] theorem Nat.factorial.eq_2 : ∀ (n_2 : Nat), n_2.succ.factorial = (n_2 + 1) * n_2.factorial
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
-/

/-
## 健全性が保たれるための条件

`partial_fixpoint` で修飾すれば停止性を証明しなくても許される関数と、そうではない関数があります。どんな関数でも `partial_fixpoint` で修飾すれば見逃してもらえるわけではありません。
-/

/--
error: failed to compile definition 'search' using `partial_fixpoint`, could not prove that the type
  {α : Type} → (Nat → Option α) → Nat → α
is nonempty.
-/
#guard_msgs (substring := true) in --#
/-- 点列 `f : Nat → Option α` が `some` を返すような最初の `f n` を返す -/
def search (f : Nat → Option α) (start : Nat) : α :=
  match f start with
  | .some x => x
  | .none => search f (start + 1)
partial_fixpoint

/-
許される関数とそうでない関数の違いはどこにあるのでしょうか？実は、`partial_fixpoint` で修飾することができる関数は、大まかに次の２つの条件のどちらかを満たすものです。[^partial-fixpoint-ref]

1. 返り値の型が [`Inhabited`](#{root}/TypeClass/Inhabited.md) であるような、末尾再帰関数
2. [`Option`](#{root}/Type/Option.md) モナドのような、適切な[モナド](#{root}/TypeClass/Monad.md)に包まれた値を返す関数

### 1-A 返り値の型が Inhabited とは

返り値の型が `Inhabited` でなければならない、という条件がなぜ必要なのかを見るには、以下のような例を考えると良いでしょう。
-/

unsafe def empty_loop : Empty := empty_loop

unsafe example : False := by
  exact empty_loop.elim

/-
停止性の保証なしに再帰関数 `f : A → B` の定義を許すと、`f` を使って `B` の項を作ることができてしまう可能性があります。したがって、`B` が `Inhabited` でなければ、矛盾が導かれる可能性があります。これを禁止するのはもっともなことでしょう。

なお、例外として定義域の型も空である場合は、返り値の型が `Inhabited` でなくても `partial_fixpoint` で修飾することができるようです。これはカリー・ハワード同型対応から言えば「矛盾を仮定すれば矛盾が示せる」ことに相当し、論理的には妥当なものの応用はないかもしれません。
-/

/-- 停止しないし返り値の型は空だが、`partial_fixpoint` で修飾できる関数 -/
def f : Empty → Empty :=
  fun x => f x
partial_fixpoint

/-
### 1-B 末尾再帰的とは

再帰関数 `f : A → B` が末尾再帰的でなければならない、という条件がなぜ必要なのか見るために、以下の例を見てください。
-/

/-- 末尾再帰的でない、停止しない関数 -/
unsafe def nonTR_loop (n : Nat) : Nat :=
  1 + nonTR_loop n

-- nonTR_loop の定義から、以下の関数等式が成り立つはず
-- (deep recursion になるので証明できず、やむを得ず axiom としている)
unsafe axiom nonTR_loop.def (n : Nat) : nonTR_loop n = 1 + nonTR_loop n

-- 矛盾が導かれる
unsafe example : False := by
  have lem : ∀ x, x ≠ 1 + x := by
    intro x
    grind

  let y := nonTR_loop 0
  have : y = 1 + y := by
    dsimp [y]
    rw [← nonTR_loop.def 0]

  exact lem y this

/-
返り値の型 `Nat` は当然ながら `Inhabited` ですが、末尾再帰的でなかったために、関数等式 `f x = 1 + f x` を満たす関数 `f` が存在することになってしまい、そんな自然数 `f x` は存在しないので矛盾が導かれてしまいました。

もしこれが末尾再帰的であれば、どうだったか？を考えるとより明確になります。たとえば以下の例を考えてみましょう。
-/

/-- 末尾再帰的な、停止しない再帰関数 -/
def tr_loop (n : Nat) : Nat :=
  tr_loop (n + 1)
partial_fixpoint

/-
`f 0 = f 1 = f 2 = ...` という関数等式を満たす `f` は確かに一意には定まらない（再帰が停止しないため）のですが、この関数の存在を仮定しても矛盾が導かれることはありません。なぜなら、定数関数という解がきちんと存在するからです。`partial_fixpoint` は、この関数 `tr_loop` の値を具体的に特定することなく、ただ `tr_loop n = tr_loop (n + 1)` という関数等式を満たす何者かであるとするだけなので、矛盾が導かれることはありません。
-/

-- tr_loop の定義から得られるのは以下の関数等式だけ
/--
info: equations:
theorem tr_loop.eq_1 : ∀ (n : Nat), tr_loop n = tr_loop (n + 1)
-/
#guard_msgs in --#
#print equations tr_loop

/-
これだけでは「なぜ末尾再帰なら大丈夫なのか」の完全な説明にはなっていませんが、とりあえず以上の例から「末尾再帰なら、`f x = f y` という形の等式が得られるだけなので、関数が停止しなくても値が一意に定まらなくなるだけで矛盾は生じない」ということが窺えるのではないでしょうか。
-/

/-
[^partial-fixpoint-ref]: Lean 公式リファレンスの「Partial Fixpoint Recursion」の項目を参照：<https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#partial-fixpoint>
-/
