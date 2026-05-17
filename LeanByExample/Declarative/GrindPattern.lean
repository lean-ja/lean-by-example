/- # grind_pattern

`grind_pattern` コマンドは、定理を [`grind`](#{root}/Tactic/Grind.md) タクティクに再利用させるためのパターンを指定するためのコマンドです。
-/

/-- 何らかの二項関係 -/
opaque R : Nat → Nat → Prop

/-- R は推移的 -/
axiom Rtrans {x y z : Nat} : R x y → R y z → R x z

-- ローカルコンテキストに `R x y` と `R y z` が現れたとき、
-- `Rtrans` をインスタンス化しなさいと grind に指示している
grind_pattern Rtrans => R x y, R y z

example (x y z : Nat) (h₁ : R x y) (h₂ : R y z) : R x z := by
  -- grind で証明できる
  grind

/-
## `[grind]` 属性では登録できない例

`[grind]` 属性を使うとパターンを自動で推測してくれますが、自動推測に失敗することがあります。
このような場合は `grind_pattern` コマンドでパターンを明示する必要があります。

{{#include ./GrindPattern/AttributeFailure.md}}
-/

/-
## where による制御

`grind_pattern` コマンドは、`grind` タクティクに定理を再利用させることができるという点では `[grind]` 属性とできることが同じですが、`grind_pattern` コマンドの方がより細かい制御を行えます。

典型的な例として、`grind_pattern` コマンドでは `where` で制約を追加することができ、不要なインスタンスが暴発することを防ぐことができます。

### `=/=` 制約

`=/=` 制約を追加すると、両辺が definitionally equal でないときにのみ定理がインスタンス化されるようになります。

{{#include ./GrindPattern/NotDefeq.md}}
-/

/- ### `guard` 制約

`guard` 制約を追加すると、与えられた条件が成り立つときにだけ定理がインスタンス化されるようになります。

`grind_pattern` コマンドでは様々なパターンが登録できるのですが、**等式を登録することはできません。**
したがって `A = B` が成り立つときにインスタンス化してほしい定理がある場合は、`guard` 制約を追加するのが良いでしょう。

{{#include ./GrindPattern/Guard.md}}

また、不等式 `A ≤ B` 等はパターンとしては登録できるのですが、動作が不安定になるためお勧めできません。なるべく `guard` 制約などとして扱うことが望ましいでしょう。

{{#include ./GrindPattern/GuardLe.md}}
-/
