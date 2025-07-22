import Playground.CS.Ch08.S01

/- ## Reasoning About Machine Executions -/
namespace Compiler

theorem getElem_int_eq_toNat {α : Type} (ls : List α) (i : Int) (pos : 0 ≤ i) (h : i < ls.length)
  : ls[i] = ls[i.toNat] := rfl

/-- プログラム P を機械状態 c で実行した結果 c' に遷移するなら, P にプログラムを付け足しても c' になる. -/
theorem exec_appendR {P c c' P'} (h : P ⊢ c →* c') : (P ++ P') ⊢ c →* c' := by
  induction h
  case refl => apply execStar.refl
  case step c c' c'' h₁ h₂ ih =>
    apply execStar.step (h₂ := ih)
    dsimp [exec1] at h₁ ⊢
    apply And.intro (right := by cases h₁; simp only [List.length_append]; omega)
    rw [h₁.left.symm]

    have : P[c.pc]! = (P ++ P')[c.pc]! := by
      have : c.pc < ↑P.length + ↑P'.length := by omega
      simp [h₁, this, getElem_int_eq_toNat]
    rw [this]

/-- exec_appendL のための補題 (Lemma 8.4) -/
theorem iexec_shift {x c c' n} :
  (iexec x { c with pc := n + c.pc } = { c' with pc := n + c'.pc }) ↔ iexec x c = c' := by
  constructor <;> intro h
  case mp =>
    unfold iexec
    split
    all_goals
      simp [iexec] at h
      try
        rcases h with ⟨h₁, h₂, h₃⟩
        simp_all
      congr
    any_goals omega
    all_goals
      split <;> simp_all <;> omega
    done
  case mpr =>
    unfold iexec
    split
    all_goals
      symm at h
      simp_all [iexec]
      try omega
    all_goals
      split <;> simp_all <;> omega
    done

/-- `P ⊢ c →* c'` の時、左に任意のプログラムP'を足してもこの関係が成り立つ. (Lemma 8.3) -/
theorem exec_appendL {P c c' P'}
  (h : P ⊢ c →* c')
  : (P' ++ P) ⊢ { c with pc := P'.length + c.pc } →* { c' with pc := P'.length + c'.pc } := by
  induction h
  case refl => apply execStar.refl
  case step c c' c'' h₁ h₂ ih =>
    apply execStar.step (h₂ := ih)
    dsimp [exec1] at h₁ ⊢
    apply And.intro (right := by cases h₁; simp only [List.length_append]; omega)
    -- rw [h₁.left.symm]

    -- この先はiexec_shiftを使って証明する
    rw [iexec_shift, h₁.left.symm]
    congr 1

    -- getElem! を getElem にする
    have h : 0 ≤ ↑P'.length + c.pc ∧ ↑P'.length + c.pc < ↑P'.length + ↑P.length := by omega
    simp [h, h₁]
    rw [getElem_append_distrib]
    case e_a.pos => omega
    case e_a.h => simp; omega
    case e_a.h' => omega

    -- ゴール中のif式は常にelse節へと評価される
    have h : ¬ (↑P'.length + c.pc < ↑P'.length) := by omega
    simp [h]
    congr
    omega

  done

/-- プログラムと機械状態遷移の推移律 (Lemma 8.5) -/
theorem exec_append_trans {P c c' P' c''}
  (c__c' : P ⊢ c →* c')
  (c'__c'' : P' ⊢ { c' with pc := c'.pc - P.length } →* c'')
  : (P ++ P') ⊢ c →* { c'' with pc := P.length + c''.pc } := by
  have := exec_appendL c'__c'' (P' := P)
  simp at this
  rw [show ↑P.length + (c'.pc - ↑P.length) = c'.pc by omega] at this
  apply execStar_execStar ?_ this
  apply exec_appendR
  exact c__c'
