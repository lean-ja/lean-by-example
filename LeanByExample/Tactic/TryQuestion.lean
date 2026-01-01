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

  -- try? なら証明を見つけることができる
  try?

end List
