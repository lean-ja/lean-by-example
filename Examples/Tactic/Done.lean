/- # done

`done` は、証明終了の合図です。証明すべきゴールが残っていない時に成功し、それ以外の時にはエラーになります。QED のようなものです。証明がサブゴールに分かれている場合、サブゴールごとに判定を行います。-/
variable (P Q : Prop)

example (h : P → Q) : ¬ P ∨ Q := by
  -- `P` が成り立つかどうかで場合分けを行う
  by_cases hP : P

  -- `P` が成り立つ場合
  case pos =>
    -- `P → Q` より `Q` が成り立つ
    have := h hP

    -- したがって結論が従う
    exact Or.inr this

    -- `P` が成り立つ場合の証明終わり.
    done

  -- `P` が成り立たない場合
  case neg =>
    -- `¬ P` が成り立つので、`¬ P ∨ Q` も成り立つ
    exact Or.inl hP

    -- `P` が成り立たない場合の証明終わり.
    done
