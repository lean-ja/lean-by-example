import Mathlib.Tactic

/-!
  # eval コマンド
-/

/-!
  ## 基本的な式の評価
  --------------------
  `eval` は式の値を評価することができます．
-/

-- 2
#eval 1 + 1

-- 実行している Lean のバージョンが表示される
#eval Lean.versionString

def w := "world"

-- 文字列が代入されて "hello, world" と表示される
#eval s!"hello, {w}"

/-!
  ## 関数の値の評価
  -----------------
  定義した関数が特定の値に対し，どのように振る舞うかテストできます
-/

-- 階乗関数
def fac : ℕ → ℕ
| 0 => 1
| n + 1 => (n + 1) * fac n

-- 120
#eval fac 5

/-!
  ## IO アクションの評価
  ----------------------
  IO アクションを実行することができます．
-/

def main : IO Unit :=
  IO.println "Hello, world!"

-- Hello, world!
#eval main
