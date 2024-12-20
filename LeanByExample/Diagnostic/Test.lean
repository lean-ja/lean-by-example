/- # \#test
`#test` コマンドは、Plausible ライブラリで定義されているもので、与えられた命題が成り立つかどうか、具体例をランダムに生成してチェックすることで検証します。[`plausible`](#{root}/Tactic/Plausible.md) タクティクと同様の機能を持ちます。
-/
import Plausible

-- 命題 `P : Prop` に対して、`#test P` で `P` が成り立つかどうかを検証する
#test ∀ (n : Nat), n + 0 = n

-- 反例が見つからなければ「反例が見つからない」と教えてくれる
/-- info: Unable to find a counter-example -/
#guard_msgs in
  #test ∀ (n : Nat), n + n = 2 * n
