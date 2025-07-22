import Playground.CS.Ch07.S01

/- ## Instructions and Stack Machine -/
namespace Compiler

variable {α : Type} (xs ys : List α)

instance : GetElem (List α) Int α (fun ls i => 0 ≤ i ∧ i < ls.length) where
  getElem xs i _ := xs[i.toNat]

/-- ### lemma 8.1
自然数ではなくて、整数によるインデックスアクセスを考えて、
インデックスアクセスの分配法則を証明する。
-/
theorem getElem_append_distrib (i : Int) (pos : 0 ≤ i) (h : i < (xs ++ ys).length) (h' : i - xs.length < ys.length)
    : (xs ++ ys)[i] = (if h : i < xs.length then xs[i] else ys[i - xs.length]) := by
  have (ls : List α) (h) : ls[i]'h = ls[i.toNat] := rfl
  simp only [this]

  -- `i : Int` を自然数に翻訳する
  have ⟨n, hn⟩ : ∃ n : Nat, i.toNat = n := by
    exists i.toNat
  simp only [hn]
  have hi : i < ↑xs.length ↔ n < xs.length := by grind
  simp only [hi]

  -- `n` が `xs` の範囲内にあるかどうかで場合分けをする
  by_cases h : n < xs.length
  · simp [h]
  · simp only [h, ↓reduceDIte]
    rw [show ys[i - xs.length] = ys[(i - xs.length).toNat] by rfl]
    simp only [Int.toNat_sub', hn]
    rw [List.getElem_append_right (by omega)]

/-- 変数名 -/
abbrev Vname := String

/-- メモリやスタックに格納されている値 -/
abbrev Val := Int

/-- machine の命令 -/
inductive Instr where
  /-- スタックのn番目を取得する -/
  | Loadi (n : Int)
  /-- 変数名が指すメモリアドレスの値を取得する -/
  | Load (x : Vname)
  /-- スタックの一番上とその下を足す -/
  | Add
  /-- 変数名が指すメモリアドレスにスタックの一番上の値を格納する -/
  | Store (x : Vname)
  /-- 今実行している命令の場所を基準に n だけジャンプする -/
  | Jmp (n : Int)
  /-- スタックの一番上とその下を比較し、二つ目の方が小さければ ジャンプする -/
  | Jmpless (n : Int)
  /-- スタックの一番上とその下を比較し、二つ目の方が大きいか等しければ ジャンプする -/
  | Jmpge (n : Int)
deriving Inhabited, Repr, DecidableEq

/-- スタック -/
abbrev Stack := List Val

/-- メモリ -/
abbrev State := Vname → Val

/-- マシンの状態 -/
structure Config where
  /-- プログラムカウンタ -/
  pc : Int
  /-- メモリ -/
  s : State
  /-- スタック -/
  stk : Stack
deriving Inhabited

/-- 機械語の実行 -/
def iexec : Instr → Config → Config
  | .Loadi n, ⟨i, s, stk⟩ => ⟨i + 1, s, n :: stk⟩
  | .Load x, ⟨i, s, stk⟩ => ⟨i + 1, s, s x :: stk⟩
  | .Add, ⟨i, s, stk⟩ => ⟨i + 1, s, (stk[1]! + stk[0]!) :: stk.drop 2⟩
  | .Store x, ⟨i, s, stk⟩ => ⟨i + 1, s[x ↦ stk[0]!], stk.drop 1⟩
  | .Jmp n, ⟨i, s, stk⟩ => ⟨i + 1 + n, s, stk⟩
  | .Jmpless n, ⟨i, s, stk⟩ =>
    ⟨if stk[1]! < stk[0]! then i + 1 + n else i + 1, s, stk.drop 2⟩
  | .Jmpge n, ⟨i, s, stk⟩ =>
    ⟨if stk[0]! ≤ stk[1]! then i + 1 + n else i + 1, s, stk.drop 2⟩

/-- プログラムPと機械状態cにおいて, `iexec` を1回実行すると状態が c' に遷移する -/
def exec1 (P : List Instr) (c c' : Config) : Prop :=
  iexec P[c.pc]! c = c' ∧ 0 ≤ c.pc ∧ c.pc < P.length

@[inherit_doc]
notation P " ⊢ " c:100 " → " c':40 => exec1 P c c'

/-- exec1 の反射的推移的閉包 -/
@[grind intro]
inductive execStar : List Instr → Config → Config → Prop
  /-- 反射的 -/
  | refl (P : List Instr) (c : Config) : execStar P c c
  /-- 推移的 -/
  | step {P c c' c''} (h₁ : P ⊢ c → c') (h₂ : execStar P c' c'') : execStar P c c''

@[inherit_doc]
notation P " ⊢ " c:100 " →* " c':40 => execStar P c c'

section Trans

  theorem exec1_exec1 {P a b c} (a_b : P ⊢ a → b) (b_c : P ⊢ b → c) : P ⊢ a →* c := by
    grind

  theorem execStar_execStar {P a b c} (a__b : P ⊢ a →* b) (b__c : P ⊢ b →* c) : P ⊢ a →* c := by
    induction a__b with grind

  theorem execStar_exec1 {P a b c} (a__b : P ⊢ a →* b) (b_c : P ⊢ b → c) : P ⊢ a →* c := by
    grind [execStar_execStar]

end Trans

def defS : State := fun _ => 0

@[simp] protected theorem getElem_cons_zero (xs : List α) (x : α) : (x :: xs)[(0 : Int)] = x := rfl
@[simp] protected theorem getElem!_cons_zero [Inhabited α] (xs : List α) (x : α) : (x :: xs)[(0 : Int)]! = x := by
  simp
@[simp] protected theorem getElem_cons_one [Inhabited α] (xs : List α) (a b : α) : (a :: b :: xs)[(1 : Int)]! = b := by
  have : 1 < (xs.length : Int) + 1 + 1 := by omega
  simp [this]
  rfl

set_option warn.sorry false in

example : ([.Load "y", .Store "x"] ⊢ ⟨0, defS["x" ↦ 3]["y" ↦ 4], []⟩ →* ⟨2, defS["x" ↦ 4]["y" ↦ 4], []⟩) := by
  apply exec1_exec1 (by simp [exec1, iexec]; rfl)
  simp [exec1, iexec]
  sorry
