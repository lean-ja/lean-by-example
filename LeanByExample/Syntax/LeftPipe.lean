/- # 左パイプライン演算子

左パイプライン演算子 `<|` は、`f <| a` と書くことで `f a` と同じ意味になります。
-/
section --#

variable {α β : Type}

example (a : α) (f : α → β) : (f <| a) = f a := by rfl

end --#
