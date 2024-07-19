/-
# native_decide
`native_decide` は、式を評価したときに判ることを示すことができます。

たとえば、Lean では再帰関数 `f` を定義したらそれが停止することの証明を求められますが、それを `sorry` で回避したとしましょう。このとき `f` の具体的な値を `#eval` で評価することは依然として可能ですが、その値をとることを `rfl` で証明することはできなくなります。

しかし、`native_decide` を使うと証明が可能です。
-/
namespace NativeDecide --#

/-- Euclide のアルゴリズム -/
def gcd (m n : Nat) : Nat :=
  if m = 0 then
    n
  else
    gcd (n % m) m

  -- 停止性を証明しない
  decreasing_by sorry

-- eval はできる
#eval gcd 42998431 120019

-- `rfl` では証明できない
-- これは停止性を証明していないため
#check_failure (by rfl : gcd 42998431 120019 = 1)

-- `native_decide` ならば証明できる
#check (by native_decide : gcd 42998431 120019 = 1)

/- 補足すると、`native_decide` を使用するときにはコンパイラを信頼することになります。具体的には `Lean.ofReduceBool` という追加の公理が使用されます。-/

theorem native : Nat.gcd 42998431 120019 = 1 := by native_decide

/-- info: 'NativeDecide.native' depends on axioms: [propext, Lean.ofReduceBool] -/
#guard_msgs in #print axioms native

/- ## 注意
`native_decide` を使うことは安全ではなく、`native_decide` を使うと簡単に `False` を示すことができます。つまり、`native_decide` を使った証明は正式な証明ではありません。-/

def one := 1

-- 間違った実装をわざと提供する
@[implemented_by one] def zero := 0

theorem zero_ne_eq_one : False := by
  have : zero ≠ one := by decide

  -- native_decide は implemented_by を真に受けるので、
  -- 実際には間違いだが示せてしまう
  have : zero = one := by native_decide

  contradiction

/-- info: 'NativeDecide.zero_ne_eq_one' depends on axioms: [Lean.ofReduceBool] -/
#guard_msgs in #print axioms zero_ne_eq_one

end NativeDecide --#
