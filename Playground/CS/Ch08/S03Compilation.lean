import Playground.CS.Ch08.S02

namespace Compiler

/-- 数値計算式 -/
inductive AExp where
  /-- 定数 -/
  | n (v : Int)
  /-- 変数 -/
  | v (name : Vname)
  /-- 足し算 -/
  | plus (a₁ a₂ : AExp)

/-- AExp を 命令列にコンパイルする -/
def acomp : AExp → List Instr
  | .n n => [.Loadi n]
  | .v x => [.Load x]
  | .plus a₁ a₂ => acomp a₁ ++ acomp a₂ ++ [Instr.Add]

/-- AExp を評価する -/
def aval : AExp → State → Val
  | .n n, _ => n
  | .v x, s => s x
  | .plus a₁ a₂, s => aval a₁ s + aval a₂ s

theorem acomp_correct (a : AExp) (s : State) (stk : List Int) :
  (acomp a) ⊢ ⟨0, s, stk⟩ →* ⟨(acomp a).length, s, aval a s :: stk⟩ := by
  induction a generalizing stk
  -- 基底ケースは同じ手順で証明できるので `all_goals` を使う. 先に `plus` の場合を証明する.
  case plus a₁ a₂ a₁_ih a₂_ih =>
    -- pos と h の補題は何度か再利用するので、ここで証明しておく.
    have h1 : ((acomp a₁).length : Int) ≥ 0 := by omega
    have h2 : ((acomp a₂).length : Int) ≥ 0 := by omega
    have pos : 0 ≤ ((acomp a₁).length : Int) + ↑(acomp a₂).length := by omega
    have h : ((acomp a₁).length : Int) + ((acomp a₂).length : Int) < (acomp a₁ ++ ((acomp a₂) ++ [Instr.Add])).length := by simp [List.length]; omega
    clear h1 h2

    -- 初期状態からa₁とa₂を実行した結果を考える.
    dsimp [acomp]
    specialize a₂_ih (aval a₁ s :: stk)
    have := @exec_append_trans (c__c' := a₁_ih stk) (P' := acomp a₂)
    simp at this; specialize this _ a₂_ih; simp at this
    clear a₁_ih a₂_ih

    -- ↑の結果は a₁ と a₂ の実行後に Add 命令を実行した場合の途中経過だと言える.
    replace this := exec_appendR this (P' := [.Add])
    -- そこから1ステップ実行すれば c' に遷移するはずである.
    let c' : Config := ⟨↑(acomp a₁ ++ acomp a₂ ++ [Instr.Add]).length, s, aval (a₁.plus a₂) s :: stk⟩

    have indexH : (acomp a₁ ++ (acomp a₂ ++ [.Add]))[((acomp a₁).length : Int) + ↑(acomp a₂).length]! = .Add := by
      rw [getElem!_pos (h := ⟨pos, h⟩)]
      rw [getElem_int_eq_toNat (pos := pos) (h := h)]
      conv => lhs; arg 2; rw [← Int.natCast_add, Int.toNat_natCast]
      rw [List.getElem_append_right (by simp), List.getElem_append_right (by omega)]
      simp

    apply execStar_exec1 (c := c') this
    simp [exec1, indexH]
    clear indexH this

    refine ⟨?_, pos, by omega⟩
    simp [iexec, aval, c']; ac_rfl

  all_goals
    apply execStar.step (h₂ := execStar.refl ..)
    simp [acomp, exec1]
    rfl

/-- 論理演算式 -/
inductive BExp where
  /-- 定数 -/
  | Bc (val : Bool)
  /-- !a -/
  | Not (exp : BExp)
  /-- a && b -/
  | And (left right : BExp)
  /-- a < b -/
  | Less (left right : AExp)

/-- 論理演算式を命令列にコンパイルする.
式expの評価結果がflagと一致する場合のみoffsetの分ジャンプする.
-/
def bcomp : (exp : BExp) → (flag : Bool) → (offset : Int) → List Instr
  | .Bc v, f, n => if v = f then [.Jmp n] else []
  | .Not b, f, n => bcomp b (!f) n
  | .And b1 b2, f, n =>
    let cb2 := bcomp b2 f n
    /-
    f が true の時は `b1 && b2` 全体が true になる時, n が示す先にジャンプしたい.
    ということは, もし b1 が false になるなら,「b2 の実行は飛ばして n が示す先にはジャンプしない」
    だから m に cb2.length が入る.
    f が false の時は `!b1 || !b2` 全体が true になる時, n が示す先にジャンプしたい.
    ということは, もし b1 が false になるなら,「b2 の実行は飛ばして n が示す先にジャンプする」
    だから m に cb2.length + n が入る.
    -/
    let m : Int := if f then cb2.length else cb2.length + n
    let cb1 := bcomp b1 false m
    cb1 ++ cb2
  | .Less a1 a2, f, n =>
    acomp a1 ++ acomp a2 ++ (if f then [.Jmpless n] else [.Jmpge n])

-- Example 8.7
#guard bcomp (.And (.Bc true) (.Bc true)) false 3 = []
#guard bcomp (.And (.Bc false) (.Bc true)) true 3 = [.Jmp 1, .Jmp 3]
#guard bcomp (.And (.Less (.v "x") (.v "y")) (.Bc true)) false 3 = [.Load "x", .Load "y", .Jmpge 3]
