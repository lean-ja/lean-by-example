/- # 16.7 コンパイラの正しさ -/

namespace PIH

/-- 数式。簡単にするために足し算だけ -/
@[grind]
inductive Expr where
  /-- 数値リテラル -/
  | val (n : Nat)
  /-- 足し算の適用 -/
  | add (l r : Expr)

/-- 式を数に直接評価する -/
@[grind]
def eval (e : Expr) : Nat :=
  match e with
  | .val n => n
  | .add l r => eval l + eval r

-- テスト
#guard
  let e := Expr.add (Expr.val 1) (Expr.val 2)
  eval e = 3

/-- スタック -/
abbrev Stack := List Nat

/-- スタックを操作する命令 -/
@[grind]
inductive Op where
  | push (n : Nat)
  | add
deriving Repr, DecidableEq

abbrev Code := List Op

/-- コードを実行する

**TODO** スタックに数が足りなくて .add 命令が実行できないときの挙動をどう定義するかはすごく重要で、
これを上手く定義しないと後に続く定理が証明できなくなったりする。
たとえば`panic!`にしてしまうと、`[]`を返すことになるので、定理のステートメントに面倒な場合分けが発生する。
-/
@[grind]
def exec (code : Code) (st : Stack) : Stack :=
  match code, st with
  | [], st => st -- コードが空ならスタックをそのまま返す
  | .push n :: code, st => exec code (n :: st) -- push命令はスタックに数値を追加
  | .add :: code, [] => exec code [] -- スタックに足すべき数が足りない場合は何もしない
  | .add :: code, [n] => exec code [n] -- スタックに足すべき数が1つしかない場合は何もしない
  | .add :: code, n1 :: n2 :: st => exec code ((n1 + n2) :: st) -- add命令はスタックの上位2つを足す

/-- 数式をコードにコンパイルする -/
@[grind]
def comp (e : Expr) : Code :=
  match e with
  | .val n => [.push n] -- 数値リテラルはpush命令に変換
  | .add l r => comp l ++ comp r ++ [.add] -- 足し算は左辺と右辺を評価してからadd命令を追加

-- テスト
#guard
  let e := Expr.add (Expr.val 1) (Expr.val 2)
  comp e = [.push 1, .push 2, .add]

#guard
  let e := Expr.add (Expr.val 1) (Expr.val 2)
  exec (comp e) [] = [3]

#eval
  let c := [.add]
  let d := [.push 1]
  let s := [2]
  let lhs := exec (c ++ d) s
  let rhs := exec d (exec c s)
  assert! lhs = rhs -- テスト
  IO.println s!"lhs = {lhs}, rhs = {rhs}"

#eval
  let c := [.push 2]
  let d := [.add]
  let s := []
  let lhs := exec (c ++ d) s
  let rhs := exec d (exec c s)
  assert! lhs = rhs -- テスト
  IO.println s!"lhs = {lhs}, rhs = {rhs}"

@[grind _=_]
theorem exec_append (c d : Code) (s : Stack) :
    exec (c ++ d) s = exec d (exec c s) := by
  fun_induction exec c s with grind

/-- コンパイラの実装の正しさを表現する定理 -/
theorem comp_eval (e : Expr) (s : Stack) : exec (comp e) s = eval e :: s := by
  induction e generalizing s with grind

-- ## comp' の定義を算出するパート
-- def comp' (e : Expr) (c : Code) := comp e ++ c

-- @[simp, grind]
-- theorem comp'_val (n : Nat) (c : Code) :
--     comp' (Expr.val n) c = .push n :: c := by
--   dsimp [comp', comp]

-- @[simp, grind]
-- theorem comp'_add (l r : Expr) (c : Code) :
--     comp' (Expr.add l r) c = comp' l (comp' r (.add :: c)) := by
--   dsimp [comp', comp]
--   ac_rfl

/-- 算出された comp'

利点
* `++` を使わないので効率が良くなった
* 証明が簡単になった！分配法則のような補題が必要なくなった。
-/
def comp' (e : Expr) (c : Code) : Code :=
  match e with
  | .val n => .push n :: c
  | .add l r => comp' l (comp' r (.add :: c))

theorem comp'_correct (e : Expr) (s : Stack) (c : Code) :
    exec (comp' e c) s = exec c (eval e :: s) := by
  fun_induction comp' e c generalizing s with grind

end PIH
