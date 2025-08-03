import Lean

-- `my_exact?` というタクティックの構文を定義する（構文として `my_exact?` を認識させる）
syntax (name := myExact?) "my_exact?" : tactic

open Lean Elab Tactic in

-- `my_exact?` タクティックの実装を定義する
@[tactic myExact?]
def evalMyExact? : Tactic := fun _stx => do
  -- 現在の環境（定理などが格納されている）を取得
  let env ← getEnv

  -- 環境中の定数を取得し、以下の条件でフィルターする：
  -- 1. unsafe な定数ではない
  -- 2. 種類が axiom か thm（定理）のもの
  let theorems : List Name := SMap.toList (Environment.constants env)
    |>.filter (fun (_name, info) => ! ConstantInfo.isUnsafe info)
    |>.filterMap (fun (name, _info) => do
        let kind ← getOriginalConstKind? env name
        match kind with
        | .axiom | .thm => name
        | _ => none
      )

  -- 条件を満たす定理に対して順に試す
  for name in theorems do
    try
      -- 名前を構文ノードに変換
      let nameStx := mkIdent name

      -- `apply name <;> assumption` を構文的に展開・実行する
      evalTactic <| ← `(tactic| apply $nameStx <;> assumption)

      -- 成功したらログを出力し、タクティックの実行を終了する
      logInfo m!"Applied {name} successfully."
      return

    catch _ =>
      -- 失敗しても続行（次の定理を試す）
      continue

  -- どの定理も適用できなかった場合はタクティックとして失敗を返す
  failure

set_option maxHeartbeats 500000 in

-- 使用例
example (x y : Nat) (h : x = y) : y = x := by
  my_exact?
