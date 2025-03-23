/- # s!

`s!` は、文字列補間を行うための構文です。
-/

def greet (name : String) : String :=
  s!"Hello, {name}!"

/-⋆-//-- info: "Hello, World!" -/
#guard_msgs in --#
#eval greet "World"
