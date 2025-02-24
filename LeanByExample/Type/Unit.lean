/- # Unit

`Unit` は、1つの要素だけを持つ型です。`Unit` が持つ唯一の項は `()` と書かれます。
-/

-- `()` は `Unit` の項
example : Unit := ()

-- `Unit` の要素は `() : Unit` のみ
example (x : Unit) : x = () := by rfl

/- 関数の返り値がないことを表現するのに、返り値の型を `Unit` にするということがよく行われます。 -/

/-⋆-//-- info: IO.println "hello" : IO Unit -/
#guard_msgs in --#
#check IO.println "hello"
