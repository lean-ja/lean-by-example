
/- # Neg

`Neg` は `-` という前置記法の単項演算子のための型クラスです。`-` 記法が何を意味するかについては制約はありません。
-/

/-- 自前で定義した自然数型 -/
inductive MyNat where
  | zero
  | succ (n : MyNat)

/-- 自前で定義した整数型 -/
inductive MyInt where
  | ofNat (n : MyNat)
  | negSucc (n : MyNat)

namespace MyInt
  /- ## MyInt のマイナス演算を定義する -/

  /-- 自然数に対するマイナス演算 -/
  def negOfNat : MyNat → MyInt
    | .zero => ofNat .zero
    | .succ m => negSucc m

  /-- 整数に対するマイナス演算 -/
  def neg (n : MyInt) : MyInt :=
    match n with
    | ofNat n => negOfNat n
    | negSucc n => ofNat n

  -- 記法が定義されていないので使えない
  #check_failure - MyInt.ofNat MyNat.zero

  -- `neg` 関数を `-` の実装とする
  instance : Neg MyInt where
    neg := neg

  -- マイナス演算記号が使えるようになった
  #check - MyInt.ofNat MyNat.zero

end MyInt
