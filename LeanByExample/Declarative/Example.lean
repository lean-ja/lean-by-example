/- # example
`example` は名前を付けずに命題の証明をすることができるコマンドです。 -/
-- `1 + 1 = 2` は `rfl` で証明できる
example : 1 + 1 = 2 := rfl

-- `n + 0 = n` は `rfl` で証明できる
example {n : Nat} : n + 0 = n := rfl

/- より正確には、`example : T := t` は `t` が型 `T` を持っていることを確かめます。特に `T` の型が [`Prop`](#{root}/Type/Prop.md) であるときには、最初に述べた通り `t` は `T` の証明だとみなすことができます。 -/

-- `[1, 2, 3]` は `List Nat` 型の項
example : List Nat := [1, 2, 3]

-- `#[1, 2, 3]` は `Array Nat` 型の項
example : Array Nat := #[1, 2, 3]

-- `true` は `Bool` 型の項
example : Bool := true
