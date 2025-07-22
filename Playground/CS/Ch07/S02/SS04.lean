import Playground.CS.Ch07.S02.SS03
/- ### 7.2.4 Equivalence of Commands -/

namespace BigStep

/-- コマンドの BigStep 意味論における同値性 -/
@[grind]
def equivCmd (S T : Stmt) : Prop := ∀ s t : State, (S, s) ==> t ↔ (T, s) ==> t

/-- `equivCmd` は反射的である -/
@[grind =>]
theorem equivCmd_refl (S : Stmt) : equivCmd S S := by
  grind

/-- `equivCmd` は対称的である -/
@[grind →]
theorem equivCmd_symm {S T : Stmt} (h : equivCmd S T) : equivCmd T S := by
  grind

/-- `equivCmd` は推移的である -/
@[grind →]
theorem equivCmd_trans {S T U : Stmt} (hST : equivCmd S T) (hTU : equivCmd T U) : equivCmd S U := by
  grind

/-- `equivCmd` は同値関係である -/
def equivCmd_equiv : Equivalence equivCmd := ⟨equivCmd_refl, equivCmd_symm, equivCmd_trans⟩

/-- `Stmt` という型に同値関係 `equivCmd` が付随しているということを宣言した -/
instance : Setoid Stmt where
  r := equivCmd
  iseqv := equivCmd_equiv

-- このように、`Stmt` の要素が同値であることを示すために `≈` を使うことができる
#check skip ≈ skip

/-- `≈` 記号の中身を展開するルールを追加する -/
syntax "unfold" "≈" : tactic
macro_rules
  | `(tactic|unfold ≈) => `(tactic| dsimp only [(· ≈ ·), Setoid.r, equivCmd])

set_option linter.unreachableTactic false in

-- big_step が `unfold ≈` を利用できるようにする
-- これでゴールに `≈` が含まれている場合に対応できる
add_big_step_rules norm [tactic (by unfold ≈)]

/-- ### Lemma 7.3
`while` 文の意味は、
* 条件式が真なら `S` を実行して再び `while` ループを実行
* 条件式が偽なら `skip`
というコマンドに等しい。 -/
theorem while_eq_if_then_skip (B : State → Prop) (S : Stmt) :
    whileDo B S ≈ ifThenElse B (S;; whileDo B S) skip := by
  big_step

/-- 排中律に関する補題 -/
@[big_step safe apply]
theorem cond_em (B : State → Prop) (s : State) : B s ∨ ¬ B s := by
  grind

/-- ### Lemma 7.4
IF 文の両方の分岐が同じコマンド `c` なら、それは `c` と同じ -/
theorem if_both_eq (B : State → Prop) (c : Stmt) : ifThenElse B c c ≈ c := by
  big_step

/-- ### Lemma 7.6
`(while b do c, s) ==> t` かつ `c ≈ c` ならば `(while b do c', s) ==> t` -/
@[grind →]
theorem while_congr {B : State → Prop} {c c' : Stmt} {s t : State} (h : c ≈ c') (h_while : (whileDo B c, s) ==> t) :
    (whileDo B c', s) ==> t := by
  -- `whileDo B C` を `x` とおく
  -- **TODO**: この generalize がないと次の induction がエラーになるのはなぜか？
  generalize hx : whileDo B c = x at h_while

  -- `h_while` に関する帰納法を使う
  -- `h_while` は BigStep のコンストラクタのどこかから来るが、
  -- `hx` を使うと `while_true` または `while_false` から来ていることが結論できる
  induction h_while <;> cases hx

  -- 条件式が偽の場合
  case while_false s' hcond => aesop

  -- 条件式が真の場合
  case while_true s' t' u' hcond' hbody' _ _hrest ih =>
    apply BigStep.while_true (t := t') (hcond := by assumption)

    case hbody =>
      -- `c ≈ c'` を使って rw することができる！（たまたま）
      rwa [← h]

    -- 帰納法の仮定を使う
    case hrest => simpa using ih

/-- ### Lemma 7.5
コマンド `c` と `c'` が同値ならば、`While` を付けても同値 -/
@[grind =>]
theorem while_eq_of_eq (B : State → Prop) (c c' : Stmt) (h : c ≈ c') : whileDo B c ≈ whileDo B c' := by
  -- ≈ の定義を展開する
  unfold ≈

  -- 状態 `s, t` が与えられたとする
  intro s t

  -- 両方向を示す
  constructor <;> intro h'

  case mp =>
    -- while_congr を使えば難しいところはすぐに終わる
    grind

  case mpr =>
    -- while_congr を使えば難しいところはすぐに終わる
    apply while_congr (h := Setoid.symm h)
    assumption

/-- セミコロン(seq)の congruence Rule -/
theorem seq_congr {S1 S2 T1 T2 : Stmt} (hS : S1 ≈ S2) (hT : T1 ≈ T2) : S1 ;; T1 ≈ S2 ;; T2 := by
  -- ≈ の定義を展開する
  unfold ≈

  -- 状態 `s, t` が与えられたとする
  intro s t

  -- 両方向を示す
  constructor <;> intro h

  case mp =>
    -- seq_iff の定義から仮定を分解する
    cases h
    case seq t hS' hT' =>
      -- 仮定を使って証明する
      apply BigStep.seq
      · rwa [← hS]
      · rwa [← hT]

  case mpr =>
    -- seq_iff の定義から仮定を分解する
    cases h
    case seq t hS' hT' =>
      -- 仮定を使って証明する
      apply BigStep.seq
      · rwa [hS]
      · rwa [hT]

/-- IF に関する congruence rule -/
theorem if_congr {B : State → Prop} {S1 S2 T1 T2 : Stmt} (hS : S1 ≈ S2) (hT : T1 ≈ T2) :
    ifThenElse B S1 T1 ≈ ifThenElse B S2 T2 := by
  -- ≈ の定義を展開する
  unfold ≈

  -- 状態 `s, t` が与えられたとする
  intro s t

  -- 両方向を示す
  constructor <;> intro h

  case mp =>
    cases h
    case if_true hcond hbody =>
      apply BigStep.if_true hcond
      rwa [← hS]

    case if_false hcond hbody =>
      apply BigStep.if_false hcond
      rwa [← hT]

  case mpr =>
    cases h
    case if_true hcond hbody =>
      apply BigStep.if_true hcond
      rwa [hS]

    case if_false hcond hbody =>
      apply BigStep.if_false hcond
      rwa [hT]

end BigStep
