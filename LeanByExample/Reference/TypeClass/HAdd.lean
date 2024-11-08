/- # HAdd
`HAdd` は、`+` という二項演算子のための型クラスです。
`+` 記法が何を意味するかについては制約はありません。
-/

structure Colour where
  red : Nat
  blue : Nat
  green : Nat
  deriving Repr

def sample : Colour := { red := 2, blue := 4, green := 8 }

-- メタ変数の番号を表示しない
set_option pp.mvars false

-- 最初は `+` 記号が定義されていないのでエラーになります。
/--
error: failed to synthesize
  HAdd Colour Colour ?_
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #eval sample + sample

/-- HAdd 型クラスのインスタンスを実装する -/
instance : HAdd Colour Colour Colour where
  hAdd c1 c2 := ⟨c1.red + c2.red, c1.blue + c2.blue, c1.green + c2.green⟩

-- 足し算記号が使えるようになった
#eval sample + sample
