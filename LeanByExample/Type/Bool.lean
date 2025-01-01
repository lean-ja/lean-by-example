/- # Bool

`Bool` は真偽値を表す型です。`true` と `false` の２つの値を持ちます。
-/

#check (true : Bool)
#check (false : Bool)

/- `Bool` の値を得るためには、たとえば `==` を用いて値を比較します。-/

inductive Foo where
  | bar
  | baz
deriving BEq

example : Bool := Foo.bar == Foo.bar
example : Bool := Foo.bar != Foo.baz

/- 真偽を表すという点で [`Prop`](./Prop.md) と似ていますが、`Bool` の項は簡約すれば必ず `true` か `false` になるため計算可能であるという含みがあります。-/
