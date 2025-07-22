/- # 第3章 型無し算術式 -/

/- ## 3.1 導入 -/
namespace TAPL

/-- ブールと数値からなる単純な式言語の項 -/
inductive Term where
  | ttrue
  | tfalse
  | tif (cond then_ else_ : Term)
  | tzero
  | tsucc (t : Term)
  | tpred (t : Term)
  | tiszero (t : Term)
deriving Inhabited, Repr, DecidableEq

-- 短く書けるようにする
export Term (ttrue tfalse tif tzero tsucc tpred tiszero)

/-- Term言語を評価する -/
partial def evalTerm (t : Term) : Option Term :=
  match t with
  | .ttrue => some ttrue -- リテラルは評価してもそのまま
  | .tfalse => some tfalse
  | .tif cond then_ else_ =>
    match evalTerm cond with
    | some .ttrue => evalTerm then_
    | some .tfalse => evalTerm else_
    | _ => none -- 条件の部分が true または false でない場合は評価できない
  | .tzero => some tzero
  | .tsucc t => some <| tsucc t
  | .tiszero t =>
    match evalTerm t with
    | some .tzero => some ttrue
    | some (tsucc _) => some tfalse
    | some (tpred (tsucc s)) => evalTerm (tiszero s)
    | _ => none -- `tiszero` の引数が数値でない場合は評価できない
  | .tpred t =>
    match evalTerm t with
    | some .tzero => some tzero
    | some (tsucc s) => evalTerm s
    | some (tpred s) => evalTerm (tpred s)
    | _ => none -- `tpred` の引数が数値でない場合は評価できない

#guard evalTerm (tiszero (tpred (tsucc tzero))) = some ttrue

/-- 数値を`Term`に変換する -/
def Term.ofNat (n : Nat) : Term :=
  match n with
  | 0 => tzero
  | n + 1 => tsucc (Term.ofNat n)

/-- `Term`の数値リテラルを数値で書けるようにする -/
instance (n : Nat) : OfNat Term n where
  ofNat := Term.ofNat n

#guard (evalTerm <| tif tfalse (0 : Term) (1 : Term)) = (1 : Term)

end TAPL
