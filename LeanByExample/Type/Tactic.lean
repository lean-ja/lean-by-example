/- # Tactic

`Lean.Elab.Tactic.Tactic` 型の項は、タクティクの内部実装を表現しています。タクティクとは証明の状態を操作する関数であり、`Tactic` 型は `Syntax → TacticM Unit` という関数型そのものです。
-/
import Lean

open Lean Elab Tactic in

example : Tactic = (Syntax → TacticM Unit) := by rfl

/- ## Tactic 型からタクティクを作る

`Tactic` 型の項からはタクティクを定義することができます。-/
/- ### tada で証明終了をお祝いするタクティク

[`done`](#{root}/Tactic/Done.md) タクティクの派生として、ゴールがなくなったら 🎉 でお祝いするタクティクを作ることができます。

{{#include ./Tactic/Tada.md}}
-/


/- ### trivial タクティクの制限版

[`trivial`](#{root}/Tactic/Trivial.md) タクティクの機能を制限し、`True` というゴールを閉じる機能だけを持つタクティクを構成することができます。[^trivial]

{{#include ./Tactic/Trivial.md}}
-/

/- ### assumption タクティク

[`assumption`](#{root}/Tactic/Assumption.md) タクティクのように、ゴールの証明が既に仮定にあるときにゴールを閉じるタクティクは次のように `Tactic` 型の関数によって実装できます。

{{#include ./Tactic/Assumption.md}}
-/

/- ### And 専用 constructor

[`constructor`](#{root}/Tactic/Constructor.md) タクティクの機能を制限し、`And` 型のゴールを分割する機能だけを持つタクティクを構成する例を示します。[^and_constructor]

{{#include ./Tactic/AndConstructor.md}}
-/

/- ### Iff 専用 constructor

[`constructor`](#{root}/Tactic/Constructor.md) タクティクの機能を制限し、`P ↔ Q` という形のゴールを分解する機能だけを持つタクティクを構成する例を示します。[^iff_constructor]

{{#include ./Tactic/IffConstructor.md}}
-/

/- ### `A₁ ∧ A₂ ∧ ... ∧ Aₙ` という形の前提から `⊢ Aᵢ` を示すタクティク
`h : A₁ ∧ A₂ ∧ ... ∧ Aₙ` という形の前提から `⊢ Aᵢ` を示すタクティクを実装する例を示します。これは引数を持つタクティクの例であるとともに、再帰的な挙動をするタクティクの例でもあります。[^destruct_and]

{{#include ./Tactic/DestructAnd.md}}
-/

/- ### `A₁ ∧ ⋯ ∧ Aₙ` という形の前提を分解して新しい仮定として追加するタクティク

再帰的な挙動をするタクティクの例として、さらに `A₁ ∧ A₂ ∧ ... ∧ Aₙ` という形の前提を分解して新しい仮定として追加するタクティクを実装する例を示します。[^cases_and]

{{#include ./Tactic/CasesAnd.md}}
-/

/- ### exact? タクティク

ゴールを直接閉じることができる定理を探すタクティクとして [`exact?`](#{root}/Tactic/ExactQuestion.md) タクティクがあります。これに相当する（しかしかなり原始的で低性能な）ものを自前で実装する例を示します。[^exact?]

{{#include ./Tactic/ExactQuestion.md}}
-/

/- [^trivial]: このコード例を書くにあたり [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide) を参考にしました。

[^and_constructor]: このコード例を書くにあたり [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide) を参考にしました。

[^iff_constructor]: このコード例を書くにあたり [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/) を参考にしました。

[^destruct_and]: このコード例を書くにあたり [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025) を参考にしました。

[^exact?]: このコード例を書くにあたり [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025) を参考にしました。

[^cases_and]: このコード例を書くにあたり [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025) の演習問題を参考にしました。
-/
