/- # opaque
`opaque` は、定義に展開できない名前を宣言するコマンドです。具体的な実装を与えずに特定の型を持つ項が「とりあえず何かある」という表現ができます。

## def との違い

[`def`](./Def.md) と異なり `opaque` コマンドを使用して宣言した名前は、`#reduce` コマンドで簡約できません。
-/

-- def を使って定義
def greet : String := "hello world!"

-- reduce の結果と eval の結果が一致する

/-- info: "hello world!" -/
#guard_msgs in #eval greet

/-- info: "hello world!" -/
#guard_msgs in #reduce greet


-- opaque を使った定義
opaque opaque_greet : String := "hello world!"

-- 簡約できないので eval と一致しなくなる

/-- info: "hello world!" -/
#guard_msgs in #eval opaque_greet

/-- info: opaque_greet -/
#guard_msgs in #reduce opaque_greet

/- `opaque` で宣言された名前は [`partial`](./Partial.md) で修飾された名前と同様に証明の中で簡約できなくなり、コンパイラを信頼しないとそれに関する証明ができなくなります。-/

-- 等しいものだという判定はできる
#eval opaque_greet == greet

-- 等しいことの証明が rfl ではできない
/--
error: tactic 'rfl' failed, the left-hand side
  opaque_greet
is not definitionally equal to the right-hand side
  greet
⊢ opaque_greet = greet
-/
#guard_msgs in example : opaque_greet = greet := by rfl

example : opaque_greet = greet := by
  -- greet は展開できるが
  dsimp [greet]

  -- opaque はできない。
  fail_if_success dsimp [opaque_greet]

  -- コンパイラを信頼することにすれば証明ができる
  native_decide

/- `opaque` で名前を宣言するとき、型だけを指定して値を指定しないということができます。このとき、その型が `Inhabited` 型クラスのインスタンスであることを暗黙のうちに使用します。-/

-- 値なしの宣言ができる
opaque some_string : String

-- 値は空文字列
/-- info: "" -/
#guard_msgs in #eval some_string

-- 適当な構造体を用意する
structure Something where
  val : String

-- Inhabited インスタンスがないのでエラーになる
/--
error: failed to synthesize
  Inhabited Something
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in opaque something : Something

/- ## variable との違い
`opaque` と同じく [`variable`](./Variable.md) コマンドも「特定の型を持つ項がとりあえず何かある」という表現をするために使用されることがありますが、両者には重要な違いがあります。

たとえば、Lean の型システムにおいて「自分自身に適用することができる関数 `f : (A → B) → C` は存在しない」ということをコードで確かめたかったとします。このとき「何でもいいので」型 `A, B, C` と関数 `f` が存在すると仮定を置きたくなります。

ここで型の宣言に [`variable`](./Variable.md) を使用すると上手くいきません。
-/
namespace opaque_test --#

variable {A B C : Type} [Inhabited C]

opaque f : (A → B) → C

-- エラーにならない！
#check f f

end opaque_test --#
/- これは、２つの `f` のそれぞれの引数としての `A, B, C` が異なる値を持ちうるためです。型を `opaque` で宣言すると固定されるので、想定通りエラーになります。 -/

opaque A : Type
opaque B : Type
opaque C : Type

-- 実装は与えないが C は Inhabited のインスタンスだと仮定
instance : Inhabited C where
  default := sorry

opaque f : (A → B) → C

-- 想定通りエラーになる
/--
error: application type mismatch
  f f
argument
  f
has type
  (A → B) → C : Type
but is expected to have type
  A → B : Type
-/
#guard_msgs (error) in #check f f
