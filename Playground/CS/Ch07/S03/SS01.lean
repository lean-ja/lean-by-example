/- ### 7.3.1 Equivalence with Big-Step Semantics
BigStep 意味論を、SmallStep に翻訳できる。
-/
import Playground.CS.Ch07.S03.SS00

open Relation

/-- Lemma 7.13: Lemma 7.12 で使う補題 -/
theorem smallStepStar_seq
  {c1 s1 c s2 c2}
  (h : (c1, s1) ⇒* (c, s2))
  : (c1 ;; c2, s1) ⇒* (c;; c2, s2) := by
  -- induction時のエラーを避けるため、一時的に(c1, s1)を変数cs1に一般化する
  generalize hcs : (c1, s1) = cs1 at h

  induction h using ReflTransGen.head_induction_on generalizing c1 s1
  case refl => aesop
  case head «c1, s1» «c1', s1'» h1 h2 ih =>
    rcases «c1', s1'» with ⟨c1', s1'⟩
    calc
      _ ⇒ (c1';; c2, s1') := by small_step
      _ ⇒* (c;; c2, s2) := by apply ih; rfl

/-- Lemma 7.12: BigStep 意味論の式を、SmallStep star に翻訳することができる。 -/
theorem big_step_to_small_step_star {S : Stmt} {s t : State} (h : (S, s) ==> t) : (S, s) ⇒* (skip, t) := by
  induction h
  case skip =>
    rfl
  case assign x a s₁ =>
    calc
      _ ⇒ (_, _) := by small_step
      _ ⇒* (_, _) := by rfl
  case seq S₁ T s₁ t₁ u₁ _hS₁ _hT hS_ih hT_ih => calc
    (S₁;; T, s₁) ⇒* (skip;; T, t₁) := smallStepStar_seq hS_ih
    _ ⇒ (T, t₁) := by small_step
    _ ⇒* (skip, u₁) := hT_ih
  case if_true B s t hCond S T _h ih => calc
    _ ⇒ (S, s) := by small_step
    _ ⇒* (skip, t) := ih
  case if_false B s t hCond S T _h ih => calc
    _ ⇒ (T, s) := by small_step
    _ ⇒* (skip, t) := ih
  case while_true B S s t u hCond _h₁ _h₂ ih₁ ih₂ => calc
    _ ⇒ (ifThenElse B (S ;; whileDo B S) skip, s) := by small_step
    _ ⇒ (S ;; whileDo B S, s) := by small_step
    _ ⇒* (skip ;; whileDo B S, t) := smallStepStar_seq ih₁
    _ ⇒ (whileDo B S, t) := by small_step
    _ ⇒* (skip, u) := ih₂
  case while_false B S s hCond => calc
    _ ⇒ (ifThenElse B (S ;; whileDo B S) skip, s) := by small_step
    _ ⇒ (skip, s) := by small_step
    _ ⇒* (skip, s) := by rfl

/-- Lemma 7.15: Lemma 7.14 の seq_stepのケース. -/
theorem small_step_star_to_big_step.seq_step {c s c' s' t}
  (h1 : (c, s) ⇒ (c', s'))
  (h2: (c', s') ==> t)
  : (c, s) ==> t := by
  induction h1 generalizing t
  case seq_step =>
    -- ****TODO****: rcases のバグではないか。確かめる。
    -- rcases h2 with ⟨t', hS', hT', s2, s3, s4⟩
    big_step
  all_goals big_step

/-- Lemma 7.14: SmallStep star 意味論の式を、BigStep に翻訳することができる。 -/
theorem small_step_star_to_big_step {S : Stmt} {s t : State}
  (h : (S, s) ⇒* (skip, t))
  : (S, s) ==> t := by
  -- induction時のエラーを避けるため、一時的に(S₁, s₁)を変数csに一般化する
  generalize hcs : (S, s) = cs at h

  induction h using ReflTransGen.head_induction_on generalizing S s
  case refl => big_step
  case head _ «S', s'» h₁ h₂ ih =>
    -- 一時的に置いた変数を消す
    simp [← hcs] at *; clear hcs

    -- Config を Stmt と State にバラす
    rcases «S', s'» with ⟨S', s'⟩
    replace h₂ : (S', s') ⇒* (skip, t) := h₂
    specialize ih rfl

    cases h₁
    case assign => cases ih; big_step
    case seq_step S S' T h₁ =>
      simp at h₁
      apply small_step_star_to_big_step.seq_step (h2 := ih)
      small_step
    case seq_skip => simpa
    case if_true => simp_all
    case if_false => simp_all
    case whileDo B S => rwa [BigStep.while_eq_if_then_skip]

/-- Corollary 7.16: BigStepとSmallStepStarの同値性 -/
theorem big_step_iff_small_step_star {c s t}
  : (c, s) ==> t ↔ (c, s) ⇒* (skip, t) := by
  constructor
  · apply big_step_to_small_step_star
  · apply small_step_star_to_big_step
