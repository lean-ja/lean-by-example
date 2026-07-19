/- # BEq

`BEq` は、`==` と `!=` による `Bool` 値の比較を提供する型クラスです。
たとえば `Nat` には `BEq` のインスタンスがあるので、2つの自然数を `==` で比較することができます。
-/

#guard 2 == 2
#guard !(2 == 3)
#guard (2 != 42)

/- ## DecidableEq との使い分け

単に `Bool` 値の比較をしたいだけであれば、`DecidableEq` のインスタンスでも可能です。しかも `DecidableEq` なら単に `Bool` 値の比較ができるだけでなく、`∀ x : α, x = x` といった「等号が満たすべきルール」もついてくるので、証明に使いたくてかつ `DecidableEq` が使える場合はそちらを使うべきでしょう。
-/

-- BEq は単なる関数なのでルールは付属しておらず、
-- x == x などを証明するには LawfulBEq が必要
example {α : Type} [BEq α] [LawfulBEq α] (x : α) : x == x := by
  simp

-- DecidableEq を仮定すると自動的に BEq と LawfulBEq のインスタンスが生成される
example {α : Type} [DecidableEq α] (x : α) : x == x := by
  let _ : LawfulBEq α := by infer_instance
  simp

/-
敢えて `BEq` を使うべきケースもあります。典型的なのは [`Float`](#{root}/Type/Float.md) です。

`Float` には `NaN` という値があります。これは「数値ではない」ことを表す特別な値で、`isNaN` という関数で判定できます。
-/

-- 0.0 / 0.0 は NaN
#guard (0.0 / 0.0).isNaN

/- `NaN` は「自分自身と比較しても等しくない」という特殊な仕様があります。 -/

-- 自分自身と比較しても false になる
#guard !((0.0 / 0.0) == (0.0 / 0.0))

-- 通常の数値の比較は true になる
#guard 3.2 == 3.2
#guard 1.45 == 1.45

/-
一方で命題としては `Float` に対しても `∀ x, x = x` が成り立っています。
-/

example (x : Float) : x = x := by rfl
