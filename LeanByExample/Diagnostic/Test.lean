/- # \#test
`#test` コマンドは、Plausible ライブラリで定義されているもので、与えられた命題が成り立つかどうか、具体例をランダムに生成してチェックすることで検証します。[`plausible`](#{root}/Tactic/Plausible.md) タクティクと同様の機能を持ちます。
-/
import Plausible

instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

section
  /- ## do 構文で実装した関数とデフォルト実装が一致することのテスト -/

  variable {α β : Type}

  /-- do 構文による map の実装 -/
  def List.doMap (f : α → β) (xs : List α) : List β := do
    let x ← xs
    return f x

  /-⋆-//-- info: Unable to find a counter-example -/
  #guard_msgs in --#
  #test
    ∀ {α β : Type} (f : α → β) (xs : List α),
    List.doMap f xs = xs.map f
end
