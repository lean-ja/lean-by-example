import Playground.CS.Ch07.S01
import Playground.CS.Tactic.BigStep

/- ## 7.2 Big-Step Semantics

### 7.2.1 Definition
-/

/-- BigStep 意味論。操作的意味論の一種。コマンドの実行前と実行後の状態だけを見て中間状態を見ないので big step と呼ばれる。
* 1つめの引数の `(c, s) : Stmt × State` は、初期状態 `s` のもとでコマンド `c` を実行することに対応。
* 2つめの引数の `t : State` は、コマンドが終了したときの状態に対応。

`BigStep (c, s) t` を、`(c, s) ==> t` と書く。
-/
@[grind]
inductive BigStep : Stmt → State → State → Prop where
  /-- skip コマンドの意味論。
  skip コマンドの実行前に状態が `s` であったなら、実行後も `s` のまま変わらない。-/
  | protected skip (s : State) : BigStep skip s s

  /-- assign コマンドの意味論。
  代入文 `x := a` の実行前に状態が `s` であったなら、代入文の実行後には状態は変数 `x` についてだけ更新される。
  `x` の値は、式 `a` を状態 `s` において評価したものに変わる。 -/
  | protected assign (x : Variable) (a : State → Nat) (s : State) : BigStep (assign x a) s (s[x ↦ a s])

  /-- seq コマンドの意味論。
  コマンド `S` により状態が `s` から `t` に変わり、 コマンド `T` により状態が `t` から `u` に変わるのであれば、
  コマンド `S;; T` により状態は `s` から `u` に変わる。-/
  | protected seq {S T : Stmt} {s t u : State} (hS : BigStep S s t) (hT : BigStep T t u) :
    BigStep (S;; T) s u

  /-- if 文の、条件式が true のときの意味論。
  コマンド `S` により状態が `s` から `t` に変わり、かつ条件式が真であるとき
  `ifThenElse B S T` により状態は `s` から `t` に変わる。 -/
  | protected if_true {B : State → Prop} {s t : State} (hcond : B s) (S T : Stmt) (hbody : BigStep S s t) :
    BigStep (ifThenElse B S T) s t

  /-- if 文の、条件式が false のときの意味論。
  コマンド `T` により状態が `s` から `t` に変わり、かつ条件式が偽であるとき
  `ifThenElse B S T` により状態は `s` から `t` に変わる。 -/
  | protected if_false {B : State → Prop} {s t : State} (hcond : ¬ B s) (S T : Stmt) (hbody : BigStep T s t) :
    BigStep (ifThenElse B S T) s t

  /-- while 文の、条件式が真のときの意味論。
  `whileDo B S` は、開始時に `B` が成り立っているなら、
  `S` を実行してから `whileDo B S` を実行するのと同じ意味になる。
  #### 補足
  `while_true` の評価は「終わらないかもしれない」ものである必要がある。だから `BigStep` を再帰関数ではなく帰納的命題として定義する必要があった。
  -/
  | while_true {B S s t u} (hcond : B s) (hbody : BigStep S s t) (hrest : BigStep (whileDo B S) t u) :
    BigStep (whileDo B S) s u

  /-- while 文の、条件式が偽のときの意味論。条件文 `B` が偽のとき、コマンド `S` の内容に関わらず、
  コマンド `whileDo B S` は状態を変化させない。-/
  | while_false {B S s} (hcond : ¬ B s) : BigStep (whileDo B S) s s

-- BigStep のための見やすい記法を用意する
@[inherit_doc] notation:55 "(" S:55 "," s:55 ")" " ==> " t:55 => BigStep S s t

section
-- ## BigStep がゴールにある場合にそれを big_step が扱えるようにする

set_option linter.unreachableTactic false

/-- skipに関するBigStepの導入則 -/
@[big_step safe apply]
theorem BigStep.skip_intro {s : State} : (skip, s) ==> s := by
  apply BigStep.skip

/-- assignに関するBigStepの導入則 -/
@[big_step safe apply]
theorem BigStep.assign_intro {x : Variable} {a : State → Nat} {s : State} :
    (assign x a, s) ==> (s[x ↦ a s]) := by
  apply BigStep.assign

/-- seqに関するBigStepの導入則 -/
@[big_step safe apply]
theorem BigStep.seq_intro {S T : Stmt} {s t u : State}
    (hS : (S, s) ==> t) (hT : (T, t) ==> u) :
    (S;; T, s) ==> u := by
  apply BigStep.seq hS hT

/-- ifThenElseに関するBigStepの導入則 -/
@[big_step unsafe 50% apply]
theorem BigStep.if_true_intro {B : State → Prop} {S T : Stmt} {s t : State}
    (hcond : B s) (hbody : (S, s) ==> t) :
    (ifThenElse B S T, s) ==> t := by
  apply BigStep.if_true hcond S T hbody

/-- whileDoに関するBigStepの導入則 -/
@[big_step unsafe 50% apply]
theorem BigStep.if_false_intro {B : State → Prop} {S T : Stmt} {s t : State}
    (hcond : ¬ B s) (hbody : (T, s) ==> t) :
    (ifThenElse B S T, s) ==> t := by
  apply BigStep.if_false hcond S T hbody

@[big_step safe apply]
theorem BigStep.while_false_intro {B S s} (hcond : ¬ B s) :
    (whileDo B S, s) ==> s := by
  apply BigStep.while_false hcond

@[big_step unsafe 50% apply]
theorem BigStep.while_true_intro {B S s t u}
    (hcond : B s) (hbody : (S, s) ==> t) (hrest : (whileDo B S, t) ==> u) :
    (whileDo B S, s) ==> u := by
  apply BigStep.while_true hcond hbody hrest

add_big_step_rules unsafe 95% tactic (by grind)

end

/-- `sillyLoop` コマンドにより、`x = 1, y = 0` という状態は `x = y = 0` という状態に変わる。-/
example : (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ==> (fun _ ↦ 0) := by
  dsimp [sillyLoop]
  big_step
