/- # try?

`try?` は、証明を探索するための標準的なタクティクです。帰納法や場合分けなどを含む複雑な証明も見つけることができます。
-/
namespace List

variable {α : Type}

@[grind]
def last? (as : List α) : Option α :=
  match as with
  | [] => none
  | [a] => some a
  | _ :: bs => last? bs

example (as : List α) : (reverse as).head? = as.last? := by
  -- grind 単体では証明ができない
  fail_if_success grind

  -- 帰納法を適当に使ってみてもダメ
  fail_if_success induction as with grind
  fail_if_success fun_induction last? <;> grind

  -- try? なら証明を見つけることができる
  try?

example (as : List α) : (reverse as).head? = as.last? := by
  -- 証明の一例
  fun_induction last? <;> grind [= last?.eq_def]

end List
