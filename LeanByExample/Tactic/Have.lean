/- # have

`have` は、証明の途中でわかったことを補題としてローカルコンテキストに追加するタクティクです。

`have h : P := ...` で `P` という命題の証明を構成し、その証明に `h` という名前を付けることができます。 -/
import Mathlib.Tactic.Ring -- `ring` のため --#

/-- 3重否定の簡略化 -/
example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp

  -- ここで`¬¬ P`が成り立つ。
  have hn2p : ¬¬ P := by
    -- なぜなら、`¬ P`であると仮定したとき
    intro hnp
    -- 仮定の`P`と矛盾するから
    contradiction

  -- これで`¬¬¬ P`と`¬¬ P`が得られたが、これは矛盾である
  contradiction

/- `have` で示した補題には必ず名前がつきます。名前を省略して `have : P := ...` とすると、自動的に `this` という名前になります。無名の補題が欲しい場合、代わりに [`show .. from`](#{root}/Syntax/Show.md) 構文を検討してみてください。-/

example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp

  -- 名前をつけないと…
  have : ¬¬ P := by
    intro hnp
    contradiction

  -- `this : ¬¬ P`という仮定が得られている
  guard_hyp this : ¬¬ P

  contradiction

/- また `have` で同じ名前を2回宣言すると、古い方はアクセス不能になってしまいます。ローカルコンテキストの補題の置き換えを行いたいときは、代わりに [`replace`](./Replace.md) を使用してください。 -/

/- ## 無名コンストラクタ

`P` の証明 `hp : P` と `Q` の証明 `hq : Q` があるとき、`P ∧ Q` の証明は `And.intro hp hq` で構成できます。ここで `And.intro` は構造体 `And` 型のコンストラクタです。

これを、コンストラクタ名を明示せずにシンプルに `⟨hp, hq⟩` と書くことができます。これは[無名コンストラクタ](#{root}/Syntax/AnonymousConstructor.md)と呼ばれるものです。-/
section
  variable (P Q : Prop) (hp : P) (hq : Q)

  def hpq : P ∧ Q := ⟨hp, hq⟩
  def hpq' : P ∧ Q := And.intro hp hq
end
/- 無名コンストラクタを利用することで、記述を簡略化できます。

### 論理積 ∧

次のように、`P ∧ Q` という命題から `P` と `Q` を取り出すことができます。-/

example (P Q : Prop) (hPQ : P ∧ Q) : P := by
  -- `P ∧ Q` という仮定を分解する
  -- `hQ : Q` は不要なのでアンダースコアに置き換える
  have ⟨ hP, _ ⟩ := hPQ

  assumption

/- ### 存在 ∃

次のように、`∃ x : X, P x` という命題から、条件を満たす `x` を取り出すことができます。`x : X` と `hx : P x` がローカルコンテキストに追加されます。 -/

-- `x` が偶数のとき `3 * x` も偶数
example (x : ℕ) (hx : ∃ y, x = 2 * y) : ∃ z, 3 * x = 2 * z := by
  -- `hx` で存在が主張されている `y` と、
  -- `x = 2 * y` という命題を得る
  have ⟨y, hy⟩ := hx
  exists 3 * y
  rw [hy]
  ring
