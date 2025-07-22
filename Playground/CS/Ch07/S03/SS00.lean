import Playground.CS.Ch07.S02.SS04
import Playground.CS.Tactic.SmallStep
import Mathlib.Logic.Relation

/- ## 7.3 Small Step Semantics -/

/-- #### SmallStep 意味論
コマンドと状態の組 `Stmt × State` を二つ受け取る。(コマンドと状態の組のことは configuration と呼ぶ)
`SmallStep (c₁, s₁) (c₂, s₂)` は、コマンド `c₁` を初期状態 `s₁` から始めて実行して、
1ステップだけ進めると状態は `s₂` になって、残りの実行すべきコマンドが `c₂` であることを表す。

引数をカリー化しないと帰納法が上手くいかない恐れがあるので注意。
-/
inductive SmallStep : Stmt → State → Stmt → State → Prop
  /-- 代入文 `x := a s` の意味論 -/
  | protected assign {x a s} : SmallStep (assign x a) s skip (s[x ↦ a s])

  /-- seq の意味論 -/
  | protected seq_step {S S' T s s'} (hS : SmallStep S s S' s') :
    SmallStep (S ;; T) s (S' ;; T) s'

  /-- skip の意味論。skip を seq してもコマンドの意味は変わらない -/
  | protected seq_skip {T s} : SmallStep (skip ;; T) s T s

  /-- 条件式が true のときの if の意味論。状態は変化せず、実行するコマンドが変化する。-/
  | protected if_true {B S T s} (hcond : B s) :
    SmallStep (ifThenElse B S T) s S s

  /-- 条件式が false のときの if の意味論。状態は変化せず、実行するコマンドが変化する。-/
  | protected if_false {B S T s} (hcond : ¬ B s) :
    SmallStep (ifThenElse B S T) s T s

  /-- while の意味論。`whileDo B S` は、`B` が真なら `S ;; whileDo B S` に等しく、
  `B` が偽なら `skip` に等しい。-/
  | protected whileDo {B S s} :
    SmallStep (whileDo B S) s (ifThenElse B (S ;; whileDo B S) skip) s

section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

-- `small_step` タクティクにコンストラクタを登録する
add_small_step_rules safe apply [
  SmallStep.assign,
  SmallStep.seq_skip,
  SmallStep.whileDo
]
add_small_step_rules unsafe 70% apply [
  SmallStep.seq_step
]
add_small_step_rules safe tactic [
  (by apply SmallStep.if_true (hcond := by assumption)),
  (by apply SmallStep.if_false (hcond := by assumption))
]
end

-- SmallStep のための見やすい記法を用意する
@[inherit_doc] notation:55 "(" c1:55 "," s1:55 ")" " ⇒ " "(" c2:55 "," s2:55 ")" => SmallStep c1 s1 c2 s2

/-- コマンドと状態を組にしたもの。configuration -/
abbrev Config := Stmt × State

/-- SmallStep の二項関係バージョン -/
abbrev smallStepBin (conf₁ conf₂ : Config) : Prop := SmallStep conf₁.1 conf₁.2 conf₂.1 conf₂.2

section
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

add_small_step_rules safe tactic [
  (by dsimp [smallStepBin] at *)
]
end

@[inherit_doc] infix:30 " ⇒ " => smallStepBin

open Relation

/-- `smallStepBin` という二項関係の反射的推移的閉包 -/
@[reducible] def smallStepStar : Config → Config → Prop :=
  ReflTransGen smallStepBin

@[inherit_doc] infix:40 " ⇒* " => smallStepStar

-- calc が使えるようにする
instance : Trans smallStepBin smallStepBin smallStepStar where
  trans a_b b_c := ReflTransGen.head a_b (ReflTransGen.head b_c .refl)
instance : Trans smallStepBin smallStepStar smallStepStar where
  trans a_b b__c := ReflTransGen.head a_b b__c
instance : Trans smallStepStar smallStepBin smallStepStar where
  trans a__b b_c := ReflTransGen.tail a__b b_c

/-- The Hitchhiker's guide to logical verification の 9.5 節より引用した例 -/
example : (sillyLoop, (fun _ => 0)["x" ↦ 1]) ⇒* (skip, (fun _ => 0)) := by
  dsimp [sillyLoop]
  calc
    _ ⇒ (_, _) := by small_step
    _ ⇒ (_, _) := by apply SmallStep.if_true; simp
    _ ⇒ (_, _) := by small_step
    _ ⇒ (_, _) := by small_step
    _ ⇒ (_, _) := by small_step
    _ ⇒ (_, _) := by small_step
    _ ⇒ (_, _) := by apply SmallStep.if_false; simp

/-- small step の one-step 評価の決定性 -/
theorem smallStep_deterministic {S T T' : Stmt} {s t t' : State}
    (h1 : (S, s) ⇒ (T, t)) (h2 : (S, s) ⇒ (T', t')) : T = T' ∧ t = t' := by
  induction h1 generalizing t' T'

  case assign x S₁ s₁ => cases h2; simp
  case seq_step S₁ T₁ S₂ s₁ s₂ hT₁ ih =>
    cases h2
    case seq_skip => cases hT₁
    case seq_step T₂ hT₂ =>
      have ih₂ := ih hT₂
      small_step
  case seq_skip S₁ s₁ =>
    cases h2
    case seq_skip => simp
    case seq_step T hT => cases hT
  case if_true B S₁ T₁ s₁ hcond =>
    cases h2; simp
    case if_false => contradiction
  case if_false B S₁ T₁ s₁ hcond =>
    cases h2
    case if_true => contradiction
    simp
  case whileDo => cases h2; simp
