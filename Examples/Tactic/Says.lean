/- # says

[exact?](./ExactQuestion.md) や [apply?](./ApplyQuestion.md) は証明を書いている過程で使用することを想定したタクティクです．`Try this: ` という提案をクリックして採用したら，`exact?` や `apply?` は提案内容で上書きされて，最終的な証明には残りません．

では，証明のある部分が `apply?` などにより提案された内容であることを明示したい場合はどうしたら良いでしょうか？`says` タクティクはまさにその問題を解決するタクティクです．提案タクティクを残しつつ，実際には実行されないようにします．

より詳しく書くと，検索タクティク `X` があり，その提案内容が `Try this: Y` だったとき，`X says` とすると `says` は `Try this: Y` の代わりに `Try this: X says Y` という提案を infoview 上で出します．
それをクリックすると，`X says` の内容が `X says Y` で置換されます．
そして，`X says Y` が実行されるときには `X` は飛ばされます．-/
import Aesop -- `aesop` のために必要 --#
import Mathlib.Init.Function -- `Injection` のために必要 --#
import Mathlib.Tactic.Says -- `says` を使うために必要

-- `says` のチェックを有効にする
set_option says.verify true

variable (P Q R S: Prop)

-- `exact?` に対して使用する例
example (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  -- `exact?` は実行されない
  exact? says
    exact hRS (hQR (hPQ hP))

/-! [simp](./Simp.md) や [aesop](./Aesop.md) のような証明自動化系のタクティクに対して，動作を軽量化しながらも証明の読みやすさを保つという目的でも使用できます．たとえば `aesop? says ...` と書かれていたら，その後のブロックでどんな複雑なことが書かれていようと，単に `aesop` の発見した証明内容を丁寧に書いているだけだとわかるわけです．-/

-- 以下 `X` `Y` `Z`を集合とする
variable {X Y Z : Type}

open Function

/-- 合成 `g ∘ f` が単射なら，`f` も単射 -/
example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  aesop? says
    intro a₁ a₂ a
    apply hgfinj
    simp_all only [comp_apply]

/-! ## オプション

`says.no_verify_in_CI : Bool` : `true` にすると，CI 環境で `X says Y` の `Y` の部分が実際に提案されている内容と一致するかのチェックが走らなくなります．-/

-- CI 環境でのチェックを無効にする
set_option says.no_verify_in_CI true

/- `says.verify : Bool` : `true` にすると，`X says Y` の `Y` のところに，実際には提案されていないタクティクを入れたときにエラーになります．-/

-- チェックを無効にする
set_option says.verify false

example (h : P → Q) (p : P) : Q := by
  -- 提案されない内容を渡してもエラーにならない
  exact? says
    try contradiction
    apply h
    exact p
