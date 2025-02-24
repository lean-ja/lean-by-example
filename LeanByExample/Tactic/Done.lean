import Lean.Elab.Tactic.Basic --#
/- # done

`done` は、証明終了の合図です。証明すべきゴールが残っていない時に成功し、それ以外の時にはエラーになります。QED のようなものです。証明がサブゴールに分かれている場合、サブゴールごとに判定を行います。-/

example (P Q : Prop) (h : P → Q) : ¬ P ∨ Q := by
  -- `P` が成り立つかどうかで場合分けを行う
  by_cases hP : P

  -- `P` が成り立つ場合
  case pos =>
    -- `P → Q` より `Q` が成り立つ
    have := h hP

    -- したがって結論が従う
    exact Or.inr this

    -- `P` が成り立つ場合の証明終わり。
    done

  -- `P` が成り立たない場合
  case neg =>
    -- `¬ P` が成り立つので、`¬ P ∨ Q` も成り立つ
    exact Or.inl hP

    -- `P` が成り立たない場合の証明終わり。
    done

/- ## 舞台裏

`getUnsolvedGoals` という関数で、現在の残りのゴールを取得することができます。これを利用すると、`done` タクティクと同様のはたらきをするタクティクを自作することができます。ここでは [`elab`](#{root}/Declarative/Elab.md) コマンドを使った実装を紹介します。
-/

open Lean.Elab Tactic Term in

elab "my_done" : tactic => do
  -- 未解決のゴールを List として取得する
  let gs ← getUnsolvedGoals

  -- ゴールが残っている場合はエラーにする
  unless gs.isEmpty do
    reportUnsolvedGoals gs
    throwAbortTactic

example : 1 = 1 := by
  rfl
  my_done

/-⋆-//--
error: unsolved goals
⊢ 2 = 2
-/
#guard_msgs in --#
example : 1 = 1 ∧ 2 = 2 := by
  refine ⟨rfl, ?_⟩
  my_done

/- これを使うと、派生タクティクを自作することもできます。ゴールを閉じたときに 🎉 でお祝いしてくれるタクティクを自作してみましょう。 -/

open Lean Elab Tactic Term in

elab "tada" : tactic => do
  let gs ← getUnsolvedGoals

  unless gs.isEmpty do
    reportUnsolvedGoals gs
    throwAbortTactic

  -- ゴールが残っていない場合はお祝いメッセージを表示する
  logInfo "Goals accomplished 🎉"

/-⋆-//-- info: Goals accomplished 🎉 -/
#guard_msgs in --#
example : 1 = 1 := by
  rfl
  tada
