/-- 2項演算の集合 -/
inductive Op where
  /-- 加法 -/
  | add
  /-- 乗法 -/
  | mul
deriving DecidableEq, Repr

/-- 数式 -/
inductive Arith where
  /-- 数値リテラル -/
  | val (n : Nat) : Arith
  /-- 演算子の適用 -/
  | app (op : Op) (lhs rhs : Arith) : Arith
deriving DecidableEq, Inhabited, Repr

section arith_syntax

  /-- `Arith` のための構文カテゴリ -/
  declare_syntax_cat arith

  /-- `Arith` を見やすく定義するための構文 -/
  syntax "[arith| " arith "]" : term

  -- 数値リテラルは数式
  syntax:max num : arith

  -- 数式を `+` または `*` で結合したものは数式
  -- `+` と `*` のパース優先順位を指定しておく
  syntax:30 arith:30 " + " arith:31 : arith
  syntax:35 arith:35 " * " arith:36 : arith

  -- 数式を括弧でくくったものは数式
  syntax:max "(" arith ")" : arith

end arith_syntax

macro_rules
  | `([arith| $n:num ]) => `(Arith.val $n)
  | `([arith| $l:arith + $r:arith]) => `(Arith.app Op.add [arith| $l] [arith| $r])
  | `([arith| $l:arith * $r:arith]) => `(Arith.app Op.mul [arith| $l] [arith| $r])
  | `([arith| ($e:arith) ]) => `([arith| $e ])
