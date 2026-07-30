/- # 右パイプライン演算子

右パイプライン演算子 `|>` は、`a |> f` と書くことで `f a` と同じ意味になります。
-/
section --#

variable {α β : Type}

example (a : α) (f : α → β) : (a |> f) = f a := by rfl

end --#
/- これがなぜ嬉しいかというと、データに関数を次々と適用して処理していくような処理を括弧なしで、自然な順序で書くことができるからです。 -/

/-- info: 20 -/
#guard_msgs in --#
#eval [1, 2, 3, 4, 5]
  |> List.filter (· % 2 = 0)
  |> List.map (· ^ 2)
  |> List.sum
