/- # try

`try` は、失敗するかもしれないタクティクをエラーにすることなく実行します。`try` で指定されたタクティクが成功した場合は `try` なしの場合と変わりませんが、失敗した場合は `try` 実行前の状態に戻ります。 -/
import Aesop -- `aesop` を使用するため

variable (P Q : Prop)

example : (P → Q) → (¬ Q → ¬ P) := by
  -- `assumption` は通らないが、エラーにならない
  try assumption

  try
    -- `aesop` が通り、証明が終了する
    aesop
    done

    -- 強制的に失敗させる
    fail

  -- `try` 実行前の状態に戻る
  show (P → Q) → ¬Q → ¬P

  aesop
