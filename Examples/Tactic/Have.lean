/- # have

`have` は，証明の途中でわかることをローカルコンテキストに追加するコマンドです．

`have h : P := ...` で `P` という命題の証明を構成し，その証明に `h` という名前を付けることができます． -/
import Mathlib.Tactic.Ring -- `ring` のため

variable (P Q R : Prop)

example (hPQ: P → Q) (hQR: Q → R) : P → R := by
  -- 示したいことが `P → R` なので，`P` だと仮定する
  intro hP

  -- 仮定 `hPQ : P → Q` と `hP : P` から `Q` が導かれる
  have hQ : Q := by exact hPQ hP

  -- 仮定 `hQR : Q → R` と `hQ : Q` から `R` が導かれる
  exact hQR hQ

/-! `have` で示した補題には必ず名前がつきます．名前を省略して `have : P := ...` とすると，自動的に `this` という名前になります．無名の補題が欲しい場合，代わりに `show` を検討してみてください．

また `have` で同じ名前を2回宣言すると，古い方はアクセス不能になってしまいます．ローカルコンテキストの補題の置き換えを行いたいときは，代わりに `replace` を使用してください． -/

/-! ## 無名コンストラクタ

`P` の証明 `hp : P` と `Q` の証明 `hq : Q` があるとき，`P ∧ Q` の証明は `And.intro hp hq` で構成できます．ここで `And.intro` は構造体 `And` 型のコンストラクタです．

これを, コンストラクタ名を明示せずにシンプルに `⟨hp, hq⟩` と書くことができます．これは[無名コンストラクタ](../Command/Structure.md#AnonymousConstructor)と呼ばれるもので，`And` に限らず任意の構造体に使用することができます．-/
variable (hp : P) (hq : Q)

def hpq : P ∧ Q := ⟨hp, hq⟩
def hpq' : P ∧ Q := And.intro hp hq

/- 無名コンストラクタを利用することで，記述を簡略化できます．

### 論理積 ∧

次のように，`P ∧ Q` という命題から `P` と `Q` を取り出すことができます．-/

example (hPQ : P ∧ Q) : P := by
  -- `P ∧ Q` という仮定を分解する
  -- `hQ : Q` は不要なのでアンダースコアに置き換える
  have ⟨ hP, _ ⟩ := hPQ

  assumption

/-! ### 存在 ∃

次のように，`∃ x: X, P x` という命題から，条件を満たす `x` を取り出すことができます．`x : X` と `hx : P x` がローカルコンテキストに追加されます． -/

-- `x`が偶数のとき`3 * x`も偶数
example (x : ℕ) (hx : ∃ y, x = 2 * y) : ∃ z, 3 * x = 2 * z := by
  -- `hx` で存在が主張されている `y` と，
  -- `x = 2 * y` という命題を得る
  have ⟨y, hy⟩ := hx
  exists 3 * y
  rw [hy]
  ring
