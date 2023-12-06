import Aesop

variable (P Q : Prop)

example : (P → Q) → (¬ Q → ¬ P) := by
  -- `assumption` は通らないが，エラーにならない
  try assumption

  try
    -- `aesop` が通り，証明が終了する
    aesop
    done

    -- 強制的に失敗させる
    fail

  -- `try` 実行前の状態に戻る
  show (P → Q) → ¬Q → ¬P

  aesop
